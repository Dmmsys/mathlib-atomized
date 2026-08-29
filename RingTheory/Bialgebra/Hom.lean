/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov, Amelia Livingston
-/
module

public import Mathlib.RingTheory.Coalgebra.Hom
public import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Homomorphisms of `R`-bialgebras

This file defines bundled homomorphisms of `R`-bialgebras. We simply mimic
`Mathlib/Algebra/Algebra/Hom.lean`.

## Main definitions

* `BialgHom R A B`: the type of `R`-bialgebra morphisms from `A` to `B`.
* `Bialgebra.counitBialgHom R A : A →ₐc[R] R`: the counit of a bialgebra as a bialgebra
  homomorphism.

## Notation

* `A →ₐc[R] B` : `R`-bialgebra homomorphism from `A` to `B`.

-/

@[expose] public section

open TensorProduct Bialgebra Coalgebra Function

universe u v w

/--
Definition of `BialgHom` / `BialgHom` 的定义

English:
structure BialgHom
  parameters: (R A B : Type*) [CommSemiring R]
  extends: A ->ₗc[R] B, A ->* B
  (no additional axioms)

中文:
结构 BialgHom
  参数: (R A B : 类型) [CommSemiring R]
  继承: A ->ₗc[R] B, A ->* B
  (无附加公理)
-/
structure BialgHom (R A B : Type*) [CommSemiring R]
    [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A ->ₗc[R] B, A ->* B

/-- Reinterpret a `BialgHom` as a `MonoidHom` -/
add_decl_doc BialgHom.toMonoidHom

@[inherit_doc BialgHom]
infixr:25 " ->ₐc " => BialgHom _

@[inherit_doc]
notation:25 A " ->ₐc[" R "] " B => BialgHom R A B

/--
Definition of `BialgHomClass` / `BialgHomClass` 的定义

English:
class BialgHomClass
  parameters: (F : Type*) (R A B : outParam Type*)
  extends: CoalgHomClass F R A B, MonoidHomClass F A B
  (no additional axioms)

中文:
类 BialgHomClass
  参数: (F : 类型) (R A B : outParam 类型)
  继承: CoalgHomClass F R A B, MonoidHomClass F A B
  (无附加公理)
-/
class BialgHomClass (F : Type*) (R A B : outParam Type*)
    [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B] : Prop
    extends CoalgHomClass F R A B, MonoidHomClass F A B

namespace BialgHomClass

variable {R A B F : Type*}

section

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B]
  [BialgHomClass F R A B]

set_option backward.isDefEq.respectTransparency false in
instance (priority := 100) toAlgHomClass : AlgHomClass F R A B where
  map_mul := map_mul
  map_one := map_one
  map_add := map_add
  map_zero := map_zero
  commutes := fun c r => by
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one]

/-- Turn an element of a type `F` satisfying `BialgHomClass F R A B` into an actual
`BialgHom`. This is declared as the default coercion from `F` to `A →ₐc[R] B`. -/
@[coe]
/--
Definition of `toBialgHom` / `toBialgHom` 的定义

English:
definition toBialgHom
  signature: (f : F)
  body: { CoalgHomClass.toCoalgHom f, AlgHomClass.toAlgHom f with
    toFun := f }

中文:
定义 toBialgHom
  签名: (f : F)
  定义体: { CoalgHomClass.toCoalgHom f, AlgHomClass.toAlgHom f with
    toFun := f }

Depends on / 依赖: AlgHomClass, AlgHomClass.toAlgHom, CoalgHomClass, CoalgHomClass.toCoalgHom, toAlgHom, toCoalgHom
-/
def toBialgHom (f : F) : A ->ₐc[R] B :=
  { CoalgHomClass.toCoalgHom f, AlgHomClass.toAlgHom f with
    toFun := f }

/--
Instance `instCoeToBialgHom` / 实例 `instCoeToBialgHom`

English:
instance instCoeToBialgHom
  signature: :
  body: ⟨BialgHomClass.toBialgHom⟩

中文:
实例 instCoeToBialgHom
  签名: :
  定义体: ⟨BialgHomClass.toBialgHom⟩

Depends on / 依赖: BialgHomClass, BialgHomClass.toBialgHom, toBialgHom
-/
instance instCoeToBialgHom :
    CoeHead F (A ->ₐc[R] B) :=
  ⟨BialgHomClass.toBialgHom⟩

end
section
variable [CommSemiring R] [Semiring A] [Bialgebra R A] [Semiring B] [Bialgebra R B]
  [FunLike F A B] [BialgHomClass F R A B]

@[simp]
/--
theorem `counitAlgHom_comp` / 定理 `counitAlgHom_comp`

English:
theorem counitAlgHom_comp
  given: (f : F)
  proof: AlgHom.toLinearMap_injective (CoalgHomClass.counit_comp f)

@[simp]

中文:
定理 counitAlgHom_comp
  条件: (f : F)
  证明: AlgHom.toLinearMap_injective (CoalgHomClass.counit_comp f)

@[simp]

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_injective, CoalgHomClass, CoalgHomClass.counit_comp, counit_comp, toLinearMap_injective
-/
theorem counitAlgHom_comp (f : F) :
    (counitAlgHom R B).comp (AlgHomClass.toAlgHom f) = counitAlgHom R A :=
  AlgHom.toLinearMap_injective (CoalgHomClass.counit_comp f)

@[simp]
/--
theorem `map_comp_comulAlgHom` / 定理 `map_comp_comulAlgHom`

English:
theorem map_comp_comulAlgHom
  given: (f : F)
  proof: AlgHom.toLinearMap_injective (CoalgHomClass.map_comp_comul f)

中文:
定理 map_comp_comulAlgHom
  条件: (f : F)
  证明: AlgHom.toLinearMap_injective (CoalgHomClass.map_comp_comul f)

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_injective, CoalgHomClass, CoalgHomClass.map_comp_comul, map_comp_comul, toLinearMap_injective
-/
theorem map_comp_comulAlgHom (f : F) :
    (Algebra.TensorProduct.map (AlgHomClass.toAlgHom f) (AlgHomClass.toAlgHom f)).comp
      (comulAlgHom R A) = (comulAlgHom R B).comp (AlgHomClass.toAlgHom f) :=
  AlgHom.toLinearMap_injective (CoalgHomClass.map_comp_comul f)

end
end BialgHomClass

namespace BialgHom

variable {R A B C D : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

section AlgebraCoalgebra

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
  [CoalgebraStruct R A] [CoalgebraStruct R B] [CoalgebraStruct R C] [CoalgebraStruct R D]

/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (A ->ₐc[R] B) A B where
  body: f.toFun
  coe_injective f g h := by
    rcases f with ⟨_, _⟩
    rcases g with ⟨_, _⟩
    simp_all

中文:
实例 funLike
  签名: : FunLike (A ->ₐc[R] B) A B where
  定义体: f.toFun
  coe_injective f g h := by
    rcases f with ⟨_, _⟩
    rcases g with ⟨_, _⟩
    simp_all

Depends on / 依赖: f.toFun
-/
instance funLike : FunLike (A ->ₐc[R] B) A B where
  coe f := f.toFun
  coe_injective f g h := by
    rcases f with ⟨_, _⟩
    rcases g with ⟨_, _⟩
    simp_all

/--
Instance `bialgHomClass` / 实例 `bialgHomClass`

English:
instance bialgHomClass
  signature: : BialgHomClass (A ->ₐc[R] B) R A B where
  body: fun f => f.map_add'
  map_smulₛₗ := fun f => f.map_smul'
  counit_comp := fun f => f.counit_comp
  map_comp_comul := fun f => f.map_comp_comul
  map_mul := fun f => f.map_mul'
  map_one := fun f => f.map_one'

中文:
实例 bialgHomClass
  签名: : BialgHomClass (A ->ₐc[R] B) R A B where
  定义体: fun f => f.map_add'
  map_smulₛₗ := fun f => f.map_smul'
  counit_comp := fun f => f.counit_comp
  map_comp_comul := fun f => f.map_comp_comul
  map_mul := fun f => f.map_mul'
  map_one := fun f => f.map_one'

Depends on / 依赖: f.map_add, map_add
-/
instance bialgHomClass : BialgHomClass (A ->ₐc[R] B) R A B where
  map_add := fun f => f.map_add'
  map_smulₛₗ := fun f => f.map_smul'
  counit_comp := fun f => f.counit_comp
  map_comp_comul := fun f => f.map_comp_comul
  map_mul := fun f => f.map_mul'
  map_one := fun f => f.map_one'

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: {R α β : Type*} [CommSemiring R]
  body: f

initialize_simps_projections BialgHom (toFun -> apply, as_prefix toCoalgHom)

@[simp]

中文:
定义 Simps.apply
  签名: {R α β : 类型} [CommSemiring R]
  定义体: f

initialize_simps_projections BialgHom (toFun -> apply, as_prefix toCoalgHom)

@[simp]
-/
def Simps.apply {R α β : Type*} [CommSemiring R]
    [Semiring α] [Algebra R α] [Semiring β]
    [Algebra R β] [CoalgebraStruct R α] [CoalgebraStruct R β]
    (f : α ->ₐc[R] β) : α -> β := f

initialize_simps_projections BialgHom (toFun -> apply, as_prefix toCoalgHom)

@[simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: {F : Type*} [FunLike F A B] [BialgHomClass F R A B] (f : F)
  proof: rfl

@[simp]

中文:
定理 coe_coe
  条件: {F : 类型} [FunLike F A B] [BialgHomClass F R A B] (f : F)
  证明: rfl

@[simp]
-/
protected theorem coe_coe {F : Type*} [FunLike F A B] [BialgHomClass F R A B] (f : F) :
    ⇑(f : A ->ₐc[R] B) = f :=
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: {f : A ->ₗc[R] B} (h h₁)
  statement: ((⟨f, h, h₁⟩ : A ->ₐc[R] B) : A -> B) = f
  proof: rfl

@[norm_cast]

中文:
定理 coe_mk
  条件: {f : A ->ₗc[R] B} (h h₁)
  结论: ((⟨f, h, h₁⟩ : A ->ₐc[R] B) : A -> B) = f
  证明: rfl

@[norm_cast]
-/
theorem coe_mk {f : A ->ₗc[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A ->ₐc[R] B) : A -> B) = f :=
  rfl

@[norm_cast]
/--
theorem `coe_mks` / 定理 `coe_mks`

English:
theorem coe_mks
  given: {f : A -> B} (h₀ h₁ h₂ h₃ h₄ h₅)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_mks
  条件: {f : A -> B} (h₀ h₁ h₂ h₃ h₄ h₅)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_mks {f : A -> B} (h₀ h₁ h₂ h₃ h₄ h₅) :
    ⇑(⟨⟨⟨⟨f, h₀⟩, h₁⟩, h₂, h₃⟩, h₄, h₅⟩ : A ->ₐc[R] B) = f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_coalgHom_mk` / 定理 `coe_coalgHom_mk`

English:
theorem coe_coalgHom_mk
  given: {f : A ->ₗc[R] B} (h h₁)
  proof: by
  rfl

@[simp, norm_cast]

中文:
定理 coe_coalgHom_mk
  条件: {f : A ->ₗc[R] B} (h h₁)
  证明: by
  rfl

@[simp, norm_cast]
-/
theorem coe_coalgHom_mk {f : A ->ₗc[R] B} (h h₁) :
    ((⟨f, h, h₁⟩ : A ->ₐc[R] B) : A ->ₗc[R] B) = f := by
  rfl

@[simp, norm_cast]
/--
theorem `coe_toCoalgHom` / 定理 `coe_toCoalgHom`

English:
theorem coe_toCoalgHom
  given: (f : A ->ₐc[R] B)
  statement: ⇑(f : A ->ₗc[R] B) = f
  proof: rfl

中文:
定理 coe_toCoalgHom
  条件: (f : A ->ₐc[R] B)
  结论: ⇑(f : A ->ₗc[R] B) = f
  证明: rfl
-/
theorem coe_toCoalgHom (f : A ->ₐc[R] B) : ⇑(f : A ->ₗc[R] B) = f :=
  rfl

/--
lemma `toCoalgHom_apply` / 引理 `toCoalgHom_apply`

English:
lemma toCoalgHom_apply
  given: (f : A ->ₐc[R] B) (a : A)
  statement: f.toCoalgHom a = f a
  proof: rfl

@[simp, norm_cast]

中文:
引理 toCoalgHom_apply
  条件: (f : A ->ₐc[R] B) (a : A)
  结论: f.toCoalgHom a = f a
  证明: rfl

@[simp, norm_cast]
-/
lemma toCoalgHom_apply (f : A ->ₐc[R] B) (a : A) : f.toCoalgHom a = f a := rfl

@[simp, norm_cast]
/--
theorem `coe_toLinearMap` / 定理 `coe_toLinearMap`

English:
theorem coe_toLinearMap
  given: (f : A ->ₐc[R] B)
  statement: ⇑(f : A ->ₗ[R] B) = f
  proof: rfl

中文:
定理 coe_toLinearMap
  条件: (f : A ->ₐc[R] B)
  结论: ⇑(f : A ->ₗ[R] B) = f
  证明: rfl
-/
theorem coe_toLinearMap (f : A ->ₐc[R] B) : ⇑(f : A ->ₗ[R] B) = f :=
  rfl

/-- Turn a bialgebra homomorphism into an algebra homomorphism. -/
@[coe]
/--
Definition of `toAlgHom` / `toAlgHom` 的定义

English:
definition toAlgHom
  signature: (f : A ->ₐc[R] B)
  body: f
  map_zero' := f.map_zero
  commutes' := by
    simp [Algebra.algebraMap_eq_smul_one, toCoalgHom_apply]

中文:
定义 toAlgHom
  签名: (f : A ->ₐc[R] B)
  定义体: f
  map_zero' := f.map_zero
  commutes' := by
    simp [Algebra.algebraMap_eq_smul_one, toCoalgHom_apply]
-/
def toAlgHom (f : A ->ₐc[R] B) : A ->ₐ[R] B where
  __ := f
  map_zero' := f.map_zero
  commutes' := by
    simp [Algebra.algebraMap_eq_smul_one, toCoalgHom_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (A ->ₐc[R] B) (A ->ₐ[R] B)
  body: ⟨toAlgHom⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Coe (A ->ₐc[R] B) (A ->ₐ[R] B)
  定义体: ⟨toAlgHom⟩

@[simp, norm_cast]

Depends on / 依赖: toAlgHom
-/
instance : Coe (A ->ₐc[R] B) (A ->ₐ[R] B) := ⟨toAlgHom⟩

@[simp, norm_cast]
/--
theorem `coe_toAlgHom` / 定理 `coe_toAlgHom`

English:
theorem coe_toAlgHom
  given: (f : A ->ₐc[R] B)
  statement: ⇑(f : A ->ₐ[R] B) = f
  proof: rfl

中文:
定理 coe_toAlgHom
  条件: (f : A ->ₐc[R] B)
  结论: ⇑(f : A ->ₐ[R] B) = f
  证明: rfl
-/
theorem coe_toAlgHom (f : A ->ₐc[R] B) : ⇑(f : A ->ₐ[R] B) = f :=
  rfl

/--
theorem `toAlgHom_toLinearMap` / 定理 `toAlgHom_toLinearMap`

English:
theorem toAlgHom_toLinearMap
  given: (f : A ->ₐc[R] B)
  proof: by
  rfl

中文:
定理 toAlgHom_toLinearMap
  条件: (f : A ->ₐc[R] B)
  证明: by
  rfl
-/
theorem toAlgHom_toLinearMap (f : A ->ₐc[R] B) :
    ((f : A ->ₐ[R] B) : A ->ₗ[R] B) = f := by
  rfl

variable (φ : A ->ₐc[R] B)

/--
theorem `coe_fn_injective` / 定理 `coe_fn_injective`

English:
theorem coe_fn_injective
  statement: @Function.Injective (A ->ₐc[R] B) (A -> B) (↑)
  proof: DFunLike.coe_injective

中文:
定理 coe_fn_injective
  结论: @Function.Injective (A ->ₐc[R] B) (A -> B) (↑)
  证明: DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_fn_injective : @Function.Injective (A ->ₐc[R] B) (A -> B) (↑) :=
  DFunLike.coe_injective

/--
theorem `coe_fn_inj` / 定理 `coe_fn_inj`

English:
theorem coe_fn_inj
  given: {φ₁ φ₂ : A ->ₐc[R] B}
  statement: (φ₁ : A -> B) = φ₂ ↔ φ₁ = φ₂
  proof: DFunLike.coe_fn_eq

中文:
定理 coe_fn_inj
  条件: {φ₁ φ₂ : A ->ₐc[R] B}
  结论: (φ₁ : A -> B) = φ₂ ↔ φ₁ = φ₂
  证明: DFunLike.coe_fn_eq

Depends on / 依赖: DFunLike, DFunLike.coe_fn_eq, coe_fn_eq
-/
theorem coe_fn_inj {φ₁ φ₂ : A ->ₐc[R] B} : (φ₁ : A -> B) = φ₂ ↔ φ₁ = φ₂ :=
  DFunLike.coe_fn_eq

/--
theorem `coe_coalgHom_injective` / 定理 `coe_coalgHom_injective`

English:
theorem coe_coalgHom_injective
  statement: Function.Injective ((↑) : (A ->ₐc[R] B) -> A ->ₗc[R] B)
  proof: fun φ₁ φ₂ H => coe_fn_injective
    show ((φ₁ : A ->ₗc[R] B) : A -> B) = ((φ₂ : A ->ₗc[R] B) : A -> B) from congr_arg _ H

中文:
定理 coe_coalgHom_injective
  结论: Function.Injective ((↑) : (A ->ₐc[R] B) -> A ->ₗc[R] B)
  证明: fun φ₁ φ₂ H => coe_fn_injective
    show ((φ₁ : A ->ₗc[R] B) : A -> B) = ((φ₂ : A ->ₗc[R] B) : A -> B) from congr_arg _ H

Depends on / 依赖: coe_fn_injective, congr_arg
-/
theorem coe_coalgHom_injective : Function.Injective ((↑) : (A ->ₐc[R] B) -> A ->ₗc[R] B) :=
fun φ₁ φ₂ H => coe_fn_injective
    show ((φ₁ : A ->ₗc[R] B) : A -> B) = ((φ₂ : A ->ₗc[R] B) : A -> B) from congr_arg _ H

/--
theorem `coe_toAlgHom_injective` / 定理 `coe_toAlgHom_injective`

English:
theorem coe_toAlgHom_injective
  statement: Function.Injective ((↑) : (A ->ₐc[R] B) -> A ->ₐ[R] B)
  proof: fun φ₁ φ₂ H => coe_fn_injective
    show ((φ₁ : A ->ₐ[R] B) : A -> B) = ((φ₂ : A ->ₐ[R] B) : A -> B) from congr_arg _ H

@[deprecated (since := "2026-05-05")] alias coe_algHom_injective := coe_toAlgHom_injective

中文:
定理 coe_toAlgHom_injective
  结论: Function.Injective ((↑) : (A ->ₐc[R] B) -> A ->ₐ[R] B)
  证明: fun φ₁ φ₂ H => coe_fn_injective
    show ((φ₁ : A ->ₐ[R] B) : A -> B) = ((φ₂ : A ->ₐ[R] B) : A -> B) from congr_arg _ H

@[deprecated (since := "2026-05-05")] alias coe_algHom_injective := coe_toAlgHom_injective

Depends on / 依赖: coe_fn_injective, congr_arg
-/
theorem coe_toAlgHom_injective : Function.Injective ((↑) : (A ->ₐc[R] B) -> A ->ₐ[R] B) :=
fun φ₁ φ₂ H => coe_fn_injective
    show ((φ₁ : A ->ₐ[R] B) : A -> B) = ((φ₂ : A ->ₐ[R] B) : A -> B) from congr_arg _ H

@[deprecated (since := "2026-05-05")] alias coe_algHom_injective := coe_toAlgHom_injective

/--
theorem `coe_linearMap_injective` / 定理 `coe_linearMap_injective`

English:
theorem coe_linearMap_injective
  statement: Function.Injective ((↑) : (A ->ₐc[R] B) -> A ->ₗ[R] B)
  proof: CoalgHom.coe_linearMap_injective.comp coe_coalgHom_injective

中文:
定理 coe_linearMap_injective
  结论: Function.Injective ((↑) : (A ->ₐc[R] B) -> A ->ₗ[R] B)
  证明: CoalgHom.coe_linearMap_injective.comp coe_coalgHom_injective

Depends on / 依赖: CoalgHom, CoalgHom.coe_linearMap_injective.comp, coe_coalgHom_injective, coe_linearMap_injective
-/
theorem coe_linearMap_injective : Function.Injective ((↑) : (A ->ₐc[R] B) -> A ->ₗ[R] B) :=
  CoalgHom.coe_linearMap_injective.comp coe_coalgHom_injective

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {φ₁ φ₂ : A ->ₐc[R] B} (H : φ₁ = φ₂) (x : A)
  statement: φ₁ x = φ₂ x
  proof: DFunLike.congr_fun H x

中文:
定理 congr_fun
  条件: {φ₁ φ₂ : A ->ₐc[R] B} (H : φ₁ = φ₂) (x : A)
  结论: φ₁ x = φ₂ x
  证明: DFunLike.congr_fun H x
-/
protected theorem congr_fun {φ₁ φ₂ : A ->ₐc[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
  DFunLike.congr_fun H x

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: (φ : A ->ₐc[R] B) {x y : A} (h : x = y)
  statement: φ x = φ y
  proof: DFunLike.congr_arg φ h

@[ext]

中文:
定理 congr_arg
  条件: (φ : A ->ₐc[R] B) {x y : A} (h : x = y)
  结论: φ x = φ y
  证明: DFunLike.congr_arg φ h

@[ext]
-/
protected theorem congr_arg (φ : A ->ₐc[R] B) {x y : A} (h : x = y) : φ x = φ y :=
  DFunLike.congr_arg φ h

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {φ₁ φ₂ : A ->ₐc[R] B} (H : forall x, φ₁ x = φ₂ x)
  statement: φ₁ = φ₂
  proof: DFunLike.ext _ _ H

@[ext high]

中文:
定理 ext
  条件: {φ₁ φ₂ : A ->ₐc[R] B} (H : 对任意 x, φ₁ x = φ₂ x)
  结论: φ₁ = φ₂
  证明: DFunLike.ext _ _ H

@[ext high]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {φ₁ φ₂ : A ->ₐc[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
  DFunLike.ext _ _ H

@[ext high]
/--
theorem `ext_of_ring` / 定理 `ext_of_ring`

English:
theorem ext_of_ring
  given: {f g : R ->ₐc[R] A} (h : f 1 = g 1)
  statement: f = g
  proof: coe_linearMap_injective (by ext; assumption)

@[simp]

中文:
定理 ext_of_ring
  条件: {f g : R ->ₐc[R] A} (h : f 1 = g 1)
  结论: f = g
  证明: coe_linearMap_injective (by ext; assumption)

@[simp]

Depends on / 依赖: coe_linearMap_injective
-/
theorem ext_of_ring {f g : R ->ₐc[R] A} (h : f 1 = g 1) : f = g :=
  coe_linearMap_injective (by ext; assumption)

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: {f : A ->ₐc[R] B} (h₀ h₁ h₂ h₃ h₄ h₅)
  proof: rfl

中文:
定理 mk_coe
  条件: {f : A ->ₐc[R] B} (h₀ h₁ h₂ h₃ h₄ h₅)
  证明: rfl
-/
theorem mk_coe {f : A ->ₐc[R] B} (h₀ h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨⟨f, h₀⟩, h₁⟩, h₂, h₃⟩, h₄, h₅⟩ : A ->ₐc[R] B) = f :=
  rfl

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : A ->ₐc[R] B) (f' : A -> B) (h : f' = ⇑f)
  body: { toCoalgHom := (f : A ->ₗc[R] B).copy f' h
    map_one' := by simp_all
    map_mul' := by intros; simp_all }

@[simp]

中文:
定义 copy
  签名: (f : A ->ₐc[R] B) (f' : A -> B) (h : f' = ⇑f)
  定义体: { toCoalgHom := (f : A ->ₗc[R] B).copy f' h
    map_one' := by simp_all
    map_mul' := by intros; simp_all }

@[simp]
-/
protected def copy (f : A ->ₐc[R] B) (f' : A -> B) (h : f' = ⇑f) : A ->ₐc[R] B :=
  { toCoalgHom := (f : A ->ₗc[R] B).copy f' h
    map_one' := by simp_all
    map_mul' := by intros; simp_all }

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

section

variable (R A)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : A ->ₐc[R] A
  body: { CoalgHom.id R A, AlgHom.id R A with }

中文:
定义 id
  签名: : A ->ₐc[R] A
  定义体: { CoalgHom.id R A, AlgHom.id R A with }
-/
@[simps!] protected def id : A ->ₐc[R] A :=
  { CoalgHom.id R A, AlgHom.id R A with }

variable {R A}

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(BialgHom.id R A) = id
  proof: rfl

@[simp]

中文:
定理 coe_id
  结论: ⇑(BialgHom.id R A) = id
  证明: rfl

@[simp]
-/
theorem coe_id : ⇑(BialgHom.id R A) = id :=
  rfl

@[simp]
/--
theorem `id_toCoalgHom` / 定理 `id_toCoalgHom`

English:
theorem id_toCoalgHom
  statement: BialgHom.id R A = CoalgHom.id R A
  proof: rfl

@[simp]

中文:
定理 id_toCoalgHom
  结论: BialgHom.id R A = CoalgHom.id R A
  证明: rfl

@[simp]
-/
theorem id_toCoalgHom : BialgHom.id R A = CoalgHom.id R A :=
  rfl

@[simp]
/--
theorem `id_toAlgHom` / 定理 `id_toAlgHom`

English:
theorem id_toAlgHom
  statement: BialgHom.id R A = AlgHom.id R A
  proof: rfl

中文:
定理 id_toAlgHom
  结论: BialgHom.id R A = AlgHom.id R A
  证明: rfl
-/
theorem id_toAlgHom : BialgHom.id R A = AlgHom.id R A :=
  rfl

end

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (φ₁ : B ->ₐc[R] C) (φ₂ : A ->ₐc[R] B)
  body: { (φ₁ : B ->ₗc[R] C).comp (φ₂ : A ->ₗc[R] B), (φ₁ : B ->ₐ[R] C).comp (φ₂ : A ->ₐ[R] B) with }

@[simp]

中文:
定义 comp
  签名: (φ₁ : B ->ₐc[R] C) (φ₂ : A ->ₐc[R] B)
  定义体: { (φ₁ : B ->ₗc[R] C).comp (φ₂ : A ->ₗc[R] B), (φ₁ : B ->ₐ[R] C).comp (φ₂ : A ->ₐ[R] B) with }

@[simp]
-/
@[simps!] def comp (φ₁ : B ->ₐc[R] C) (φ₂ : A ->ₐc[R] B) : A ->ₐc[R] C :=
  { (φ₁ : B ->ₗc[R] C).comp (φ₂ : A ->ₗc[R] B), (φ₁ : B ->ₐ[R] C).comp (φ₂ : A ->ₐ[R] B) with }

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (φ₁ : B ->ₐc[R] C) (φ₂ : A ->ₐc[R] B)
  statement: ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (φ₁ : B ->ₐc[R] C) (φ₂ : A ->ₐc[R] B)
  结论: ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂
  证明: rfl

@[simp]
-/
theorem coe_comp (φ₁ : B ->ₐc[R] C) (φ₂ : A ->ₐc[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ :=
  rfl

@[simp]
/--
theorem `comp_toCoalgHom` / 定理 `comp_toCoalgHom`

English:
theorem comp_toCoalgHom
  given: (φ₁ : B ->ₐc[R] C) (φ₂ : A ->ₐc[R] B)
  proof: rfl

@[simp]

中文:
定理 comp_toCoalgHom
  条件: (φ₁ : B ->ₐc[R] C) (φ₂ : A ->ₐc[R] B)
  证明: rfl

@[simp]
-/
theorem comp_toCoalgHom (φ₁ : B ->ₐc[R] C) (φ₂ : A ->ₐc[R] B) :
    φ₁.comp φ₂ = (φ₁ : B ->ₗc[R] C).comp (φ₂ : A ->ₗc[R] B) :=
  rfl

@[simp]
/--
theorem `comp_toAlgHom` / 定理 `comp_toAlgHom`

English:
theorem comp_toAlgHom
  given: (φ₁ : B ->ₐc[R] C) (φ₂ : A ->ₐc[R] B)
  proof: rfl

@[simp]

中文:
定理 comp_toAlgHom
  条件: (φ₁ : B ->ₐc[R] C) (φ₂ : A ->ₐc[R] B)
  证明: rfl

@[simp]
-/
theorem comp_toAlgHom (φ₁ : B ->ₐc[R] C) (φ₂ : A ->ₐc[R] B) :
    φ₁.comp φ₂ = (φ₁ : B ->ₐ[R] C).comp (φ₂ : A ->ₐ[R] B) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  statement: φ.comp (BialgHom.id R A) = φ
  proof: ext fun _x => rfl

@[simp]

中文:
定理 comp_id
  结论: φ.comp (BialgHom.id R A) = φ
  证明: ext fun _x => rfl

@[simp]
-/
theorem comp_id : φ.comp (BialgHom.id R A) = φ :=
  ext fun _x => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  statement: (BialgHom.id R B).comp φ = φ
  proof: ext fun _x => rfl

中文:
定理 id_comp
  结论: (BialgHom.id R B).comp φ = φ
  证明: ext fun _x => rfl
-/
theorem id_comp : (BialgHom.id R B).comp φ = φ :=
  ext fun _x => rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (φ₁ : C ->ₐc[R] D) (φ₂ : B ->ₐc[R] C) (φ₃ : A ->ₐc[R] B)
  proof: ext fun _x => rfl

中文:
定理 comp_assoc
  条件: (φ₁ : C ->ₐc[R] D) (φ₂ : B ->ₐc[R] C) (φ₃ : A ->ₐc[R] B)
  证明: ext fun _x => rfl
-/
theorem comp_assoc (φ₁ : C ->ₐc[R] D) (φ₂ : B ->ₐc[R] C) (φ₃ : A ->ₐc[R] B) :
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
  signature: : Monoid (A ->ₐc[R] A) where
  body: comp
  mul_assoc _ _ _ := rfl
  one := BialgHom.id R A
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl

@[simp]

中文:
实例 End
  签名: : Monoid (A ->ₐc[R] A) where
  定义体: comp
  mul_assoc _ _ _ := rfl
  one := BialgHom.id R A
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl

@[simp]
-/
instance End : Monoid (A ->ₐc[R] A) where
  mul := comp
  mul_assoc _ _ _ := rfl
  one := BialgHom.id R A
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl

@[simp]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (x : A)
  statement: (1 : A ->ₐc[R] A) x = x
  proof: rfl

@[simp]

中文:
定理 one_apply
  条件: (x : A)
  结论: (1 : A ->ₐc[R] A) x = x
  证明: rfl

@[simp]
-/
theorem one_apply (x : A) : (1 : A ->ₐc[R] A) x = x :=
  rfl

@[simp]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (φ ψ : A ->ₐc[R] A) (x : A)
  statement: (φ * ψ) x = φ (ψ x)
  proof: rfl

中文:
定理 mul_apply
  条件: (φ ψ : A ->ₐc[R] A) (x : A)
  结论: (φ * ψ) x = φ (ψ x)
  证明: rfl
-/
theorem mul_apply (φ ψ : A ->ₐc[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
  rfl

end AlgebraCoalgebra

variable [Bialgebra R A] [Bialgebra R B]

/-- Construct a bialgebra hom from an algebra hom respecting counit and comultiplication. -/
@[simps!]
/--
Definition of `ofAlgHom` / `ofAlgHom` 的定义

English:
definition ofAlgHom
  signature: (f : A ->ₐ[R] B) (counit_comp : (counitAlgHom R B).comp f = counitAlgHom R A)
  body: f
  map_smul' := map_smul f
  counit_comp := congr(($counit_comp).toLinearMap)
  map_comp_comul := congr(($map_comp_comul).toLinearMap)

@[simp]

中文:
定义 ofAlgHom
  签名: (f : A ->ₐ[R] B) (counit_comp : (counitAlgHom R B).comp f = counitAlgHom R A)
  定义体: f
  map_smul' := map_smul f
  counit_comp := congr(($counit_comp).toLinearMap)
  map_comp_comul := congr(($map_comp_comul).toLinearMap)

@[simp]
-/
def ofAlgHom (f : A ->ₐ[R] B) (counit_comp : (counitAlgHom R B).comp f = counitAlgHom R A)
    (map_comp_comul :
      (Algebra.TensorProduct.map f f).comp (comulAlgHom _ _) = (comulAlgHom _ _).comp f) :
    A ->ₐc[R] B where
  __ := f
  map_smul' := map_smul f
  counit_comp := congr(($counit_comp).toLinearMap)
  map_comp_comul := congr(($map_comp_comul).toLinearMap)

@[simp]
/--
theorem `counitAlgHom_comp` / 定理 `counitAlgHom_comp`

English:
theorem counitAlgHom_comp
  given: (f : A ->ₐc[R] B)
  proof: AlgHom.toLinearMap_injective (CoalgHomClass.counit_comp f)

@[simp]

中文:
定理 counitAlgHom_comp
  条件: (f : A ->ₐc[R] B)
  证明: AlgHom.toLinearMap_injective (CoalgHomClass.counit_comp f)

@[simp]

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_injective, CoalgHomClass, CoalgHomClass.counit_comp, counit_comp, toLinearMap_injective
-/
theorem counitAlgHom_comp (f : A ->ₐc[R] B) :
    (counitAlgHom R B).comp f = counitAlgHom R A :=
  AlgHom.toLinearMap_injective (CoalgHomClass.counit_comp f)

@[simp]
/--
theorem `map_comp_comulAlgHom` / 定理 `map_comp_comulAlgHom`

English:
theorem map_comp_comulAlgHom
  given: (f : A ->ₐc[R] B)
  proof: AlgHom.toLinearMap_injective (CoalgHomClass.map_comp_comul f)

中文:
定理 map_comp_comulAlgHom
  条件: (f : A ->ₐc[R] B)
  证明: AlgHom.toLinearMap_injective (CoalgHomClass.map_comp_comul f)

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_injective, CoalgHomClass, CoalgHomClass.map_comp_comul, map_comp_comul, toLinearMap_injective
-/
theorem map_comp_comulAlgHom (f : A ->ₐc[R] B) :
    (Algebra.TensorProduct.map f f).comp (comulAlgHom R A) = (comulAlgHom R B).comp f :=
  AlgHom.toLinearMap_injective (CoalgHomClass.map_comp_comul f)

end BialgHom

namespace Bialgebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]

variable (R A) in
/--
Definition of `unitBialgHom` / `unitBialgHom` 的定义

English:
definition unitBialgHom
  signature: : R ->ₐc[R] A
  body: .ofAlgHom (Algebra.ofId R A) (by ext) (by ext)

中文:
定义 unitBialgHom
  签名: : R ->ₐc[R] A
  定义体: .ofAlgHom (Algebra.ofId R A) (by ext) (by ext)

Depends on / 依赖: Algebra, Algebra.ofId, ofAlgHom
-/
noncomputable def unitBialgHom : R ->ₐc[R] A :=
  .ofAlgHom (Algebra.ofId R A) (by ext) (by ext)

variable (R A) in
/--
Definition of `counitBialgHom` / `counitBialgHom` 的定义

English:
definition counitBialgHom
  signature: : A ->ₐc[R] R
  body: { Coalgebra.counitCoalgHom R A, counitAlgHom R A with }

@[simp]

中文:
定义 counitBialgHom
  签名: : A ->ₐc[R] R
  定义体: { Coalgebra.counitCoalgHom R A, counitAlgHom R A with }

@[simp]

Depends on / 依赖: Coalgebra, Coalgebra.counitCoalgHom, counitAlgHom, counitCoalgHom
-/
noncomputable def counitBialgHom : A ->ₐc[R] R :=
  { Coalgebra.counitCoalgHom R A, counitAlgHom R A with }

@[simp]
/--
theorem `counitBialgHom_apply` / 定理 `counitBialgHom_apply`

English:
theorem counitBialgHom_apply
  given: (x : A)
  proof: rfl

@[simp]

中文:
定理 counitBialgHom_apply
  条件: (x : A)
  证明: rfl

@[simp]
-/
theorem counitBialgHom_apply (x : A) :
    counitBialgHom R A x = Coalgebra.counit x := rfl

@[simp]
/--
theorem `counitBialgHom_toCoalgHom` / 定理 `counitBialgHom_toCoalgHom`

English:
theorem counitBialgHom_toCoalgHom
  proof: rfl

中文:
定理 counitBialgHom_toCoalgHom
  证明: rfl
-/
theorem counitBialgHom_toCoalgHom :
    counitBialgHom R A = Coalgebra.counitCoalgHom R A := rfl

/--
lemma `counitBialgHom_self` / 引理 `counitBialgHom_self`

English:
lemma counitBialgHom_self
  statement: counitBialgHom R R = .id R R
  proof: rfl

中文:
引理 counitBialgHom_self
  结论: counitBialgHom R R = .id R R
  证明: rfl
-/
@[simp] lemma counitBialgHom_self : counitBialgHom R R = .id R R := rfl

/--
Instance `subsingleton_to_ring` / 实例 `subsingleton_to_ring`

English:
instance subsingleton_to_ring
  signature: : Subsingleton (A ->ₐc[R] R)
  body: ⟨fun _ _ => BialgHom.coe_coalgHom_injective (Subsingleton.elim _ _)⟩

@[ext high]

中文:
实例 subsingleton_to_ring
  签名: : Subsingleton (A ->ₐc[R] R)
  定义体: ⟨fun _ _ => BialgHom.coe_coalgHom_injective (Subsingleton.elim _ _)⟩

@[ext high]

Depends on / 依赖: BialgHom, BialgHom.coe_coalgHom_injective, Subsingleton, Subsingleton.elim, coe_coalgHom_injective
-/
instance subsingleton_to_ring : Subsingleton (A ->ₐc[R] R) :=
  ⟨fun _ _ => BialgHom.coe_coalgHom_injective (Subsingleton.elim _ _)⟩

@[ext high]
/--
theorem `ext_to_ring` / 定理 `ext_to_ring`

English:
theorem ext_to_ring
  given: (f g : A ->ₐc[R] R)
  statement: f = g
  proof: Subsingleton.elim _ _

中文:
定理 ext_to_ring
  条件: (f g : A ->ₐc[R] R)
  结论: f = g
  证明: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem ext_to_ring (f g : A ->ₐc[R] R) : f = g := Subsingleton.elim _ _

end Bialgebra
