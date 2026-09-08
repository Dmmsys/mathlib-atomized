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

/-- Given `R`-algebras `A, B` with comultiplication maps `Δ_A, Δ_B` and counit maps
`ε_A, ε_B`, an `R`-bialgebra homomorphism `A →ₐc[R] B` is an `R`-algebra map `f` such that
`ε_B ∘ f = ε_A` and `(f ⊗ f) ∘ Δ_A = Δ_B ∘ f`. -/
/-
**BialgHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (A : Type u_2) →     (B : Type u_3) →       [inst : Com
mSemiring R] →         [inst_1 : Semiring A] →           [inst_2 : Algebra R A] 
→             [inst_3 : Semiring B] →               [inst_4 : Algebra R B] → [Co
algebraStruct R A] → [CoalgebraStruct R B] → Type (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `R`-algebras `A, B` with comultiplication maps `Δ_A, Δ_B` and counit maps
`ε_A, ε_B`, an `R`-bialgebra homomorphism `A →ₐc[R] B` is an `R`-algebra map `f`
 such that
`ε_B ∘ f = ε_A` and `(f ⊗ f) ∘ Δ_A = Δ_B ∘ f`.
-/
structure BialgHom (R A B : Type*) [CommSemiring R]
    [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A →ₗc[R] B, A →* B

/-- Reinterpret a `BialgHom` as a `MonoidHom` -/
add_decl_doc BialgHom.toMonoidHom

@[inherit_doc BialgHom]
infixr:25 " →ₐc " => BialgHom _

@[inherit_doc]
notation:25 A " →ₐc[" R "] " B => BialgHom R A B

/-- `BialgHomClass F R A B` asserts `F` is a type of bundled bialgebra homomorphisms
from `A` to `B`. -/
/-
**BialgHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (R : outParam (Type u_2)) →     (A : outParam (Type u_3
)) →       (B : outParam (Type u_4)) →         [inst : CommSemiring R] →        
   [inst_1 : Semiring A] →             [inst_2 : Algebra R A] →               [i
nst_3 : Semiring B] →                 [inst_4 : Algebra R B] → [CoalgebraStruct 
R A] → [CoalgebraStruct R B] → [FunLike F A B] → Prop
参数：Type u_2；Type u_3；Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BialgHomClass F R A B` asserts `F` is a type of bundled bialgebra homomorphisms
from `A` to `B`.
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
/-
**BialgHomClass.** 是 Mathlib 中的一个实例，位于命名空间 `BialgHomClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
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
/-
**BialgHomClass.toBialgHom** 是 Mathlib 中的一个定义，位于命名空间 `BialgHomClass`。
形式化陈述：toBialgHom (f : F) : A ->ₐc[R] B
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHomClass.toCoalgHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)
} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   
{inst_1 : Semiring …
· 使用定理 `BialgHomClass.toAlgHomClass`：∀ {R : Type u_1} {A : Type u_2} {B : Type u
_3} {F : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Alg
ebra R A] [inst_3…

--- 原说明 ---
Turn an element of a type `F` satisfying `BialgHomClass F R A B` into an actual
`BialgHom`. This is declared as the default coercion from `F` to `A →ₐc[R] B`.
-/
def toBialgHom (f : F) : A →ₐc[R] B :=
  { CoalgHomClass.toCoalgHom f, AlgHomClass.toAlgHom f with
    toFun := f }
/-
**BialgHomClass.instCoeToBialgHom** 是 Mathlib 中的一个实例，位于命名空间 `BialgHomClass`。
形式化陈述：instCoeToBialgHom : CoeHead F (A ->ₐc[R] B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoeToBialgHom :
    CoeHead F (A →ₐc[R] B) :=
  ⟨BialgHomClass.toBialgHom⟩

end
section
variable [CommSemiring R] [Semiring A] [Bialgebra R A] [Semiring B] [Bialgebra R B]
  [FunLike F A B] [BialgHomClass F R A B]

@[simp]
/-
**BialgHomClass.counitAlgHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `BialgHomClass`。
形式化陈述：counitAlgHom_comp (f : F) : (counitAlgHom R B).comp (AlgHomClass.toAlgHom 
f) = counitAlgHom R A
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.toLinearMap_injective`：toLinearMap_injective : Function.Injective
 (toLinearMap : _ -> A ->ₗ[R] B)
· 使用定理 `BialgHomClass.toAlgHomClass`：∀ {R : Type u_1} {A : Type u_2} {B : Type u
_3} {F : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Alg
ebra R A] [inst_3…
· 使用定理 `CoalgHomClass.counit_comp`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A
 : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {ins
t_1 : AddCommMo…
· 使用定理 `BialgHomClass.toCoalgHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)
} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   
{inst_1 : Semiring …
-/
theorem counitAlgHom_comp (f : F) :
    (counitAlgHom R B).comp (AlgHomClass.toAlgHom f) = counitAlgHom R A :=
  AlgHom.toLinearMap_injective (CoalgHomClass.counit_comp f)

@[simp]
/-
**BialgHomClass.map_comp_comulAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `BialgHomClass`。
形式化陈述：map_comp_comulAlgHom (f : F) : (Algebra.TensorProduct.map (AlgHomClass.toA
lgHom f) (AlgHomClass.toAlgHom f)).comp (comulAlgHom R A) = (comulAlgHom R B).co
mp (AlgHomClass.toAlgHom f)
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.toLinearMap_injective`：toLinearMap_injective : Function.Injective
 (toLinearMap : _ -> A ->ₗ[R] B)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `BialgHomClass.toAlgHomClass`：∀ {R : Type u_1} {A : Type u_2} {B : Type u
_3} {F : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Alg
ebra R A] [inst_3…
· 使用定理 `CoalgHomClass.map_comp_comul`：∀ {F : Type u_1} {R : outParam (Type u_2)}
 {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {
inst_1 : AddCommMo…
· 使用定理 `BialgHomClass.toCoalgHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)
} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   
{inst_1 : Semiring …
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

/-
**BialgHom.funLike** 是 Mathlib 中的一个实例，位于命名空间 `BialgHom`。
形式化陈述：funLike : FunLike (A ->ₐc[R] B) A B where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (A →ₐc[R] B) A B where
  coe f := f.toFun
  coe_injective f g h := by
    rcases f with ⟨_, _⟩
    rcases g with ⟨_, _⟩
    simp_all
/-
**BialgHom.bialgHomClass** 是 Mathlib 中的一个实例，位于命名空间 `BialgHom`。
形式化陈述：bialgHomClass : BialgHomClass (A ->ₐc[R] B) R A B where map_add
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddHom.map_add'`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [inst_
1 : Add N] (self : M →ₙ+ N) (x y : M),   self.toFun (x + y) = self.toFun x + sel
f.toF…
· 使用定理 `LinearMap.map_smul'`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring 
R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_
2 : AddCo…
· 使用定理 `CoalgHom.counit_comp`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [in
st : CommSemiring R] [inst_1 : AddCommMonoid A]   [inst_2 : _root_.Module R A] [
inst_3 : A…
· 使用定理 `CoalgHom.map_comp_comul`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : AddCommMonoid A]   [inst_2 : _root_.Module R A
] [inst_3 : A…
· 使用定理 `BialgHom.map_mul'`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst 
: CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semir
ing B] …
· 使用定理 `BialgHom.map_one'`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst 
: CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semir
ing B] …
-/
instance bialgHomClass : BialgHomClass (A →ₐc[R] B) R A B where
  map_add := fun f => f.map_add'
  map_smulₛₗ := fun f => f.map_smul'
  counit_comp := fun f => f.counit_comp
  map_comp_comul := fun f => f.map_comp_comul
  map_mul := fun f => f.map_mul'
  map_one := fun f => f.map_one'

/-- See Note [custom simps projection] -/
/-
**BialgHom.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `BialgHom.Simps`。
形式化陈述：{R : Type u_6} →   {α : Type u_7} →     {β : Type u_8} →       [inst : Com
mSemiring R] →         [inst_1 : Semiring α] →           [inst_2 : Algebra R α] 
→             [inst_3 : Semiring β] →               [inst_4 : Algebra R β] →    
             [inst_5 : CoalgebraStruct R α] → [inst_6 : CoalgebraStruct R β] → (
α →ₐc[R] β) → α → β
参数：α →ₐc[R] β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.apply {R α β : Type*} [CommSemiring R]
    [Semiring α] [Algebra R α] [Semiring β]
    [Algebra R β] [CoalgebraStruct R α] [CoalgebraStruct R β]
    (f : α →ₐc[R] β) : α → β := f

initialize_simps_projections BialgHom (toFun → apply, as_prefix toCoalgHom)

@[simp]
/-
**BialgHom.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Alge
bra R B] [inst_5 : CoalgebraStruct R A] [inst_6 : CoalgebraStruct R B]   {F : Ty
pe u_6} [inst_7 : FunLike F A B] [inst_8 : BialgHomClass F R A B] (f : F), ⇑↑f =
 ⇑f
参数：f : F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_coe {F : Type*} [FunLike F A B] [BialgHomClass F R A B] (f : F) :
    ⇑(f : A →ₐc[R] B) = f :=
  rfl

@[simp]
/-
**BialgHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：coe_mk {f : A ->ₗc[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A ->ₐc[R] B) : A -> B) = 
f
参数：h h₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk {f : A →ₗc[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A →ₐc[R] B) : A → B) = f :=
  rfl

@[norm_cast]
/-
**BialgHom.coe_mks** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：coe_mks {f : A -> B} (h₀ h₁ h₂ h₃ h₄ h₅) : ⇑(⟨⟨⟨⟨f, h₀⟩, h₁⟩, h₂, h₃⟩, h₄,
 h₅⟩ : A ->ₐc[R] B) = f
参数：h₀ h₁ h₂ h₃ h₄ h₅。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mks {f : A → B} (h₀ h₁ h₂ h₃ h₄ h₅) :
    ⇑(⟨⟨⟨⟨f, h₀⟩, h₁⟩, h₂, h₃⟩, h₄, h₅⟩ : A →ₐc[R] B) = f :=
  rfl

@[simp, norm_cast]
/-
**BialgHom.coe_coalgHom_mk** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：coe_coalgHom_mk {f : A ->ₗc[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A ->ₐc[R] B) : A
 ->ₗc[R] B) = f
参数：h h₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHomClass.toCoalgHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)
} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   
{inst_1 : Semiring …
-/
theorem coe_coalgHom_mk {f : A →ₗc[R] B} (h h₁) :
    ((⟨f, h, h₁⟩ : A →ₐc[R] B) : A →ₗc[R] B) = f := by
  rfl

@[simp, norm_cast]
/-
**BialgHom.coe_toCoalgHom** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：coe_toCoalgHom (f : A ->ₐc[R] B) : ⇑(f : A ->ₗc[R] B) = f
参数：f : A ->ₐc[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHomClass.toCoalgHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)
} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   
{inst_1 : Semiring …
-/
theorem coe_toCoalgHom (f : A →ₐc[R] B) : ⇑(f : A →ₗc[R] B) = f :=
  rfl
/-
**BialgHom.toCoalgHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `BialgHom`。
形式化陈述：toCoalgHom_apply (f : A ->ₐc[R] B) (a : A) : f.toCoalgHom a = f a
参数：f : A ->ₐc[R] B；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toCoalgHom_apply (f : A →ₐc[R] B) (a : A) : f.toCoalgHom a = f a := rfl

@[simp, norm_cast]
/-
**BialgHom.coe_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：coe_toLinearMap (f : A ->ₐc[R] B) : ⇑(f : A ->ₗ[R] B) = f
参数：f : A ->ₐc[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
· 使用定理 `BialgHomClass.toCoalgHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)
} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   
{inst_1 : Semiring …
-/
theorem coe_toLinearMap (f : A →ₐc[R] B) : ⇑(f : A →ₗ[R] B) = f :=
  rfl

/-- Turn a bialgebra homomorphism into an algebra homomorphism. -/
@[coe]
/-
**BialgHom.toAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `BialgHom`。
形式化陈述：toAlgHom (f : A ->ₐc[R] B) : A ->ₐ[R] B where __
参数：f : A ->ₐc[R] B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHom.map_one'`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst 
: CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semir
ing B] …
· 使用定理 `BialgHom.map_mul'`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst 
: CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semir
ing B] …

--- 原说明 ---
Turn a bialgebra homomorphism into an algebra homomorphism.
-/
def toAlgHom (f : A →ₐc[R] B) : A →ₐ[R] B where
  __ := f
  map_zero' := f.map_zero
  commutes' := by
    simp [Algebra.algebraMap_eq_smul_one, toCoalgHom_apply]
/-
**BialgHom.** 是 Mathlib 中的一个实例，位于命名空间 `BialgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (A →ₐc[R] B) (A →ₐ[R] B) := ⟨toAlgHom⟩

@[simp, norm_cast]
/-
**BialgHom.coe_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：coe_toAlgHom (f : A ->ₐc[R] B) : ⇑(f : A ->ₐ[R] B) = f
参数：f : A ->ₐc[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAlgHom (f : A →ₐc[R] B) : ⇑(f : A →ₐ[R] B) = f :=
  rfl
/-
**BialgHom.toAlgHom_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：toAlgHom_toLinearMap (f : A ->ₐc[R] B) : ((f : A ->ₐ[R] B) : A ->ₗ[R] B) =
 f
参数：f : A ->ₐc[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
-/
theorem toAlgHom_toLinearMap (f : A →ₐc[R] B) :
    ((f : A →ₐ[R] B) : A →ₗ[R] B) = f := by
  rfl

variable (φ : A →ₐc[R] B)
/-
**BialgHom.coe_fn_injective** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：coe_fn_injective : @Function.Injective (A ->ₐc[R] B) (A -> B) (↑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_fn_injective : @Function.Injective (A →ₐc[R] B) (A → B) (↑) :=
  DFunLike.coe_injective
/-
**BialgHom.coe_fn_inj** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：coe_fn_inj {φ₁ φ₂ : A ->ₐc[R] B} : (φ₁ : A -> B) = φ₂ ↔ φ₁ = φ₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_fn_eq`：coe_fn_eq {f g : F} : (f : forall a : α, β a) = (g :
 forall a : α, β a) ↔ f = g
-/
theorem coe_fn_inj {φ₁ φ₂ : A →ₐc[R] B} : (φ₁ : A → B) = φ₂ ↔ φ₁ = φ₂ :=
  DFunLike.coe_fn_eq
/-
**BialgHom.coe_coalgHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：coe_coalgHom_injective : Function.Injective ((↑) : (A ->ₐc[R] B) -> A ->ₗc
[R] B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHomClass.toCoalgHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)
} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   
{inst_1 : Semiring …
· 使用定理 `BialgHom.coe_fn_injective`：coe_fn_injective : @Function.Injective (A ->ₐ
c[R] B) (A -> B) (↑)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem coe_coalgHom_injective : Function.Injective ((↑) : (A →ₐc[R] B) → A →ₗc[R] B) :=
  fun φ₁ φ₂ H => coe_fn_injective <|
    show ((φ₁ : A →ₗc[R] B) : A → B) = ((φ₂ : A →ₗc[R] B) : A → B) from congr_arg _ H
/-
**BialgHom.coe_toAlgHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：coe_toAlgHom_injective : Function.Injective ((↑) : (A ->ₐc[R] B) -> A ->ₐ[
R] B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHom.coe_fn_injective`：coe_fn_injective : @Function.Injective (A ->ₐ
c[R] B) (A -> B) (↑)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem coe_toAlgHom_injective : Function.Injective ((↑) : (A →ₐc[R] B) → A →ₐ[R] B) :=
  fun φ₁ φ₂ H => coe_fn_injective <|
    show ((φ₁ : A →ₐ[R] B) : A → B) = ((φ₂ : A →ₐ[R] B) : A → B) from congr_arg _ H

@[deprecated (since := "2026-05-05")] alias coe_algHom_injective := coe_toAlgHom_injective
/-
**BialgHom.coe_linearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：coe_linearMap_injective : Function.Injective ((↑) : (A ->ₐc[R] B) -> A ->ₗ
[R] B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
· 使用定理 `CoalgHom.coe_linearMap_injective`：coe_linearMap_injective : Function.Inj
ective ((↑) : (A ->ₗc[R] B) -> A ->ₗ[R] B)
· 使用定理 `BialgHom.coe_coalgHom_injective`：coe_coalgHom_injective : Function.Injec
tive ((↑) : (A ->ₐc[R] B) -> A ->ₗc[R] B)
-/
theorem coe_linearMap_injective : Function.Injective ((↑) : (A →ₐc[R] B) → A →ₗ[R] B) :=
  CoalgHom.coe_linearMap_injective.comp coe_coalgHom_injective
/-
**BialgHom.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Alge
bra R B] [inst_5 : CoalgebraStruct R A] [inst_6 : CoalgebraStruct R B]   {φ₁ φ₂ 
: A →ₐc[R] B}, φ₁ = φ₂ → ∀ (x : A), φ₁ x = φ₂ x
参数：x : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected theorem congr_fun {φ₁ φ₂ : A →ₐc[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
  DFunLike.congr_fun H x
/-
**BialgHom.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [inst_4 : Alge
bra R B] [inst_5 : CoalgebraStruct R A] [inst_6 : CoalgebraStruct R B]   (φ : A 
→ₐc[R] B) {x y : A}, x = y → φ x = φ y
参数：φ : A →ₐc[R] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
-/
protected theorem congr_arg (φ : A →ₐc[R] B) {x y : A} (h : x = y) : φ x = φ y :=
  DFunLike.congr_arg φ h

@[ext]
/-
**BialgHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：ext {φ₁ φ₂ : A ->ₐc[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = φ₂
参数：H : forall x, φ₁ x = φ₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {φ₁ φ₂ : A →ₐc[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
  DFunLike.ext _ _ H

@[ext high]
/-
**BialgHom.ext_of_ring** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：ext_of_ring {f g : R ->ₐc[R] A} (h : f 1 = g 1) : f = g
参数：h : f 1 = g 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHom.coe_linearMap_injective`：coe_linearMap_injective : Function.Inj
ective ((↑) : (A ->ₐc[R] B) -> A ->ₗ[R] B)
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
· 使用定理 `BialgHomClass.toCoalgHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)
} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   
{inst_1 : Semiring …
-/
theorem ext_of_ring {f g : R →ₐc[R] A} (h : f 1 = g 1) : f = g :=
  coe_linearMap_injective (by ext; assumption)

@[simp]
/-
**BialgHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：mk_coe {f : A ->ₐc[R] B} (h₀ h₁ h₂ h₃ h₄ h₅) : (⟨⟨⟨⟨f, h₀⟩, h₁⟩, h₂, h₃⟩, 
h₄, h₅⟩ : A ->ₐc[R] B) = f
参数：h₀ h₁ h₂ h₃ h₄ h₅。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_coe {f : A →ₐc[R] B} (h₀ h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨⟨f, h₀⟩, h₁⟩, h₂, h₃⟩, h₄, h₅⟩ : A →ₐc[R] B) = f :=
  rfl

/-- Copy of a `BialgHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
/-
**BialgHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `BialgHom`。
形式化陈述：{R : Type u_1} →   {A : Type u_2} →     {B : Type u_3} →       [inst : Com
mSemiring R] →         [inst_1 : Semiring A] →           [inst_2 : Semiring B] →
             [inst_3 : Algebra R A] →               [inst_4 : Algebra R B] →    
             [inst_5 : CoalgebraStruct R A] →                   [inst_6 : Coalge
braStruct R B] → (f : A →ₐc[R] B) → (f' : A → B) → f' = ⇑f → A →ₐc[R] B
参数：f : A →ₐc[R] B；f' : A → B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `BialgHom` with a new `toFun` equal to the old one. Useful to fix defi
nitional
equalities.
-/
protected def copy (f : A →ₐc[R] B) (f' : A → B) (h : f' = ⇑f) : A →ₐc[R] B :=
  { toCoalgHom := (f : A →ₗc[R] B).copy f' h
    map_one' := by simp_all
    map_mul' := by intros; simp_all }

@[simp]
/-
**BialgHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：coe_copy (f : A ->ₗc[R] B) (f' : A -> B) (h : f' = ⇑f) : ⇑(f.copy f' h) = 
f'
参数：f : A ->ₗc[R] B；f' : A -> B；h : f' = ⇑f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : A →ₗc[R] B) (f' : A → B) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**BialgHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：copy_eq (f : A ->ₗc[R] B) (f' : A -> B) (h : f' = ⇑f) : f.copy f' h = f
参数：f : A ->ₗc[R] B；f' : A -> B；h : f' = ⇑f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : A →ₗc[R] B) (f' : A → B) (h : f' = ⇑f) : f.copy f' h = f :=
  DFunLike.ext' h

section

variable (R A)

/-- Identity map as a `BialgHom`. -/
/-
**BialgHom.id** 是 Mathlib 中的一个定义，位于命名空间 `BialgHom`。
形式化陈述：(R : Type u_1) →   (A : Type u_2) →     [inst : CommSemiring R] →       [i
nst_1 : Semiring A] → [inst_2 : Algebra R A] → [inst_3 : CoalgebraStruct R A] → 
A →ₐc[R] A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identity map as a `BialgHom`.
-/
@[simps!] protected def id : A →ₐc[R] A :=
  { CoalgHom.id R A, AlgHom.id R A with }

variable {R A}

@[simp, norm_cast]
/-
**BialgHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：coe_id : ⇑(BialgHom.id R A) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(BialgHom.id R A) = id :=
  rfl

@[simp]
/-
**BialgHom.id_toCoalgHom** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：id_toCoalgHom : BialgHom.id R A = CoalgHom.id R A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHomClass.toCoalgHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)
} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   
{inst_1 : Semiring …
-/
theorem id_toCoalgHom : BialgHom.id R A = CoalgHom.id R A :=
  rfl

@[simp]
/-
**BialgHom.id_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：id_toAlgHom : BialgHom.id R A = AlgHom.id R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_toAlgHom : BialgHom.id R A = AlgHom.id R A :=
  rfl

end

/-- Composition of bialgebra homomorphisms. -/
/-
**BialgHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `BialgHom`。
形式化陈述：{R : Type u_1} →   {A : Type u_2} →     {B : Type u_3} →       {C : Type u
_4} →         [inst : CommSemiring R] →           [inst_1 : Semiring A] →       
      [inst_2 : Semiring B] →               [inst_3 : Semiring C] →             
    [inst_4 : Algebra R A] →                   [inst_5 : Algebra R B] →         
            [inst_6 : Algebra R C] →                       [inst_7 : CoalgebraSt
ruct R A] →                         [inst_8 : CoalgebraStruct R B] →            
               [inst_9 : CoalgebraStruct R C] → (B →ₐc[R] C) → (A →ₐc[R] B) → A 
→ₐc[R] C
参数：B →ₐc[R] C；A →ₐc[R] B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of bialgebra homomorphisms.
-/
@[simps!] def comp (φ₁ : B →ₐc[R] C) (φ₂ : A →ₐc[R] B) : A →ₐc[R] C :=
  { (φ₁ : B →ₗc[R] C).comp (φ₂ : A →ₗc[R] B), (φ₁ : B →ₐ[R] C).comp (φ₂ : A →ₐ[R] B) with }

@[simp]
/-
**BialgHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：coe_comp (φ₁ : B ->ₐc[R] C) (φ₂ : A ->ₐc[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂
参数：φ₁ : B ->ₐc[R] C；φ₂ : A ->ₐc[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (φ₁ : B →ₐc[R] C) (φ₂ : A →ₐc[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ :=
  rfl

@[simp]
/-
**BialgHom.comp_toCoalgHom** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：comp_toCoalgHom (φ₁ : B ->ₐc[R] C) (φ₂ : A ->ₐc[R] B) : φ₁.comp φ₂ = (φ₁ :
 B ->ₗc[R] C).comp (φ₂ : A ->ₗc[R] B)
参数：φ₁ : B ->ₐc[R] C；φ₂ : A ->ₐc[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHomClass.toCoalgHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)
} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   
{inst_1 : Semiring …
-/
theorem comp_toCoalgHom (φ₁ : B →ₐc[R] C) (φ₂ : A →ₐc[R] B) :
    φ₁.comp φ₂ = (φ₁ : B →ₗc[R] C).comp (φ₂ : A →ₗc[R] B) :=
  rfl

@[simp]
/-
**BialgHom.comp_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：comp_toAlgHom (φ₁ : B ->ₐc[R] C) (φ₂ : A ->ₐc[R] B) : φ₁.comp φ₂ = (φ₁ : B
 ->ₐ[R] C).comp (φ₂ : A ->ₐ[R] B)
参数：φ₁ : B ->ₐc[R] C；φ₂ : A ->ₐc[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_toAlgHom (φ₁ : B →ₐc[R] C) (φ₂ : A →ₐc[R] B) :
    φ₁.comp φ₂ = (φ₁ : B →ₐ[R] C).comp (φ₂ : A →ₐ[R] B) :=
  rfl

@[simp]
/-
**BialgHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：comp_id : φ.comp (BialgHom.id R A) = φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHom.ext`：ext {φ₁ φ₂ : A ->ₐc[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁
 = φ₂
-/
theorem comp_id : φ.comp (BialgHom.id R A) = φ :=
  ext fun _x => rfl

@[simp]
/-
**BialgHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：id_comp : (BialgHom.id R B).comp φ = φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHom.ext`：ext {φ₁ φ₂ : A ->ₐc[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁
 = φ₂
-/
theorem id_comp : (BialgHom.id R B).comp φ = φ :=
  ext fun _x => rfl
/-
**BialgHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：comp_assoc (φ₁ : C ->ₐc[R] D) (φ₂ : B ->ₐc[R] C) (φ₃ : A ->ₐc[R] B) : (φ₁.
comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃)
参数：φ₁ : C ->ₐc[R] D；φ₂ : B ->ₐc[R] C；φ₃ : A ->ₐc[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHom.ext`：ext {φ₁ φ₂ : A ->ₐc[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁
 = φ₂
-/
theorem comp_assoc (φ₁ : C →ₐc[R] D) (φ₂ : B →ₐc[R] C) (φ₃ : A →ₐc[R] B) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
  ext fun _x => rfl
/-
**BialgHom.map_smul_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：map_smul_of_tower {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A
 B R' R] (r : R') (x : A) : φ (r • x) = r • φ x
参数：r : R'；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
-/
theorem map_smul_of_tower {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A B R' R] (r : R')
    (x : A) : φ (r • x) = r • φ x :=
  φ.toLinearMap.map_smul_of_tower r x

@[simps -isSimp toSemigroup_toMul_mul toOne_one]
/-
**BialgHom.End** 是 Mathlib 中的一个实例，位于命名空间 `BialgHom`。
形式化陈述：End : Monoid (A ->ₐc[R] A) where mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance End : Monoid (A →ₐc[R] A) where
  mul := comp
  mul_assoc _ _ _ := rfl
  one := BialgHom.id R A
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl

@[simp]
/-
**BialgHom.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：one_apply (x : A) : (1 : A ->ₐc[R] A) x = x
参数：x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (x : A) : (1 : A →ₐc[R] A) x = x :=
  rfl

@[simp]
/-
**BialgHom.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：mul_apply (φ ψ : A ->ₐc[R] A) (x : A) : (φ * ψ) x = φ (ψ x)
参数：φ ψ : A ->ₐc[R] A；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (φ ψ : A →ₐc[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
  rfl

end AlgebraCoalgebra

variable [Bialgebra R A] [Bialgebra R B]

/-- Construct a bialgebra hom from an algebra hom respecting counit and comultiplication. -/
@[simps!]
/-
**BialgHom.ofAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `BialgHom`。
形式化陈述：ofAlgHom (f : A ->ₐ[R] B) (counit_comp : (counitAlgHom R B).comp f = couni
tAlgHom R A) (map_comp_comul : (Algebra.TensorProduct.map f f).comp (comulAlgHom
 _ _) = (comulAlgHom _ _).comp f) : A ->ₐc[R] B where __
参数：f : A ->ₐ[R] B；counit_comp : (counitAlgHom R B).comp f = counitAlgHom R A；map
_comp_comul : (Algebra.TensorProduct.map f f).comp (comulAlgHom _ _) = (comulAlg
Hom _ _).comp f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bialgebra hom from an algebra hom respecting counit and comultiplica
tion.
-/
def ofAlgHom (f : A →ₐ[R] B) (counit_comp : (counitAlgHom R B).comp f = counitAlgHom R A)
    (map_comp_comul :
      (Algebra.TensorProduct.map f f).comp (comulAlgHom _ _) = (comulAlgHom _ _).comp f) :
    A →ₐc[R] B where
  __ := f
  map_smul' := map_smul f
  counit_comp := congr(($counit_comp).toLinearMap)
  map_comp_comul := congr(($map_comp_comul).toLinearMap)

@[simp]
/-
**BialgHom.counitAlgHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：counitAlgHom_comp (f : A ->ₐc[R] B) : (counitAlgHom R B).comp f = counitAl
gHom R A
参数：f : A ->ₐc[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.toLinearMap_injective`：toLinearMap_injective : Function.Injective
 (toLinearMap : _ -> A ->ₗ[R] B)
· 使用定理 `CoalgHomClass.counit_comp`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A
 : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {ins
t_1 : AddCommMo…
· 使用定理 `BialgHomClass.toCoalgHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)
} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   
{inst_1 : Semiring …
-/
theorem counitAlgHom_comp (f : A →ₐc[R] B) :
    (counitAlgHom R B).comp f = counitAlgHom R A :=
  AlgHom.toLinearMap_injective (CoalgHomClass.counit_comp f)

@[simp]
/-
**BialgHom.map_comp_comulAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `BialgHom`。
形式化陈述：map_comp_comulAlgHom (f : A ->ₐc[R] B) : (Algebra.TensorProduct.map f f).c
omp (comulAlgHom R A) = (comulAlgHom R B).comp f
参数：f : A ->ₐc[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.toLinearMap_injective`：toLinearMap_injective : Function.Injective
 (toLinearMap : _ -> A ->ₗ[R] B)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `CoalgHomClass.map_comp_comul`：∀ {F : Type u_1} {R : outParam (Type u_2)}
 {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {
inst_1 : AddCommMo…
· 使用定理 `BialgHomClass.toCoalgHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)
} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   
{inst_1 : Semiring …
-/
theorem map_comp_comulAlgHom (f : A →ₐc[R] B) :
    (Algebra.TensorProduct.map f f).comp (comulAlgHom R A) = (comulAlgHom R B).comp f :=
  AlgHom.toLinearMap_injective (CoalgHomClass.map_comp_comul f)

end BialgHom

namespace Bialgebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]

variable (R A) in
/-- The unit of a bialgebra as a `BialgHom`. -/
/-
**Bialgebra.unitBialgHom** 是 Mathlib 中的一个定义，位于命名空间 `Bialgebra`。
形式化陈述：unitBialgHom : R ->ₐc[R] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit of a bialgebra as a `BialgHom`.
-/
noncomputable def unitBialgHom : R →ₐc[R] A :=
  .ofAlgHom (Algebra.ofId R A) (by ext) (by ext)

variable (R A) in
/-- The counit of a bialgebra as a `BialgHom`. -/
/-
**Bialgebra.counitBialgHom** 是 Mathlib 中的一个定义，位于命名空间 `Bialgebra`。
形式化陈述：counitBialgHom : A ->ₐc[R] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit of a bialgebra as a `BialgHom`.
-/
noncomputable def counitBialgHom : A →ₐc[R] R :=
  { Coalgebra.counitCoalgHom R A, counitAlgHom R A with }

@[simp]
/-
**Bialgebra.counitBialgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra`。
形式化陈述：counitBialgHom_apply (x : A) : counitBialgHom R A x = Coalgebra.counit x
参数：x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem counitBialgHom_apply (x : A) :
    counitBialgHom R A x = Coalgebra.counit x := rfl

@[simp]
/-
**Bialgebra.counitBialgHom_toCoalgHom** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra`。
形式化陈述：counitBialgHom_toCoalgHom : counitBialgHom R A = Coalgebra.counitCoalgHom 
R A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHomClass.toCoalgHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)
} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   
{inst_1 : Semiring …
-/
theorem counitBialgHom_toCoalgHom :
    counitBialgHom R A = Coalgebra.counitCoalgHom R A := rfl
/-
**Bialgebra.counitBialgHom_self** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R], Bialgebra.counitBialgHom R R = B
ialgHom.id R R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma counitBialgHom_self : counitBialgHom R R = .id R R := rfl
/-
**Bialgebra.subsingleton_to_ring** 是 Mathlib 中的一个实例，位于命名空间 `Bialgebra`。
形式化陈述：subsingleton_to_ring : Subsingleton (A ->ₐc[R] R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `BialgHom.coe_coalgHom_injective`：coe_coalgHom_injective : Function.Injec
tive ((↑) : (A ->ₐc[R] B) -> A ->ₗc[R] B)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `BialgHomClass.toCoalgHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)
} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   
{inst_1 : Semiring …
-/
instance subsingleton_to_ring : Subsingleton (A →ₐc[R] R) :=
  ⟨fun _ _ => BialgHom.coe_coalgHom_injective (Subsingleton.elim _ _)⟩

@[ext high]
/-
**Bialgebra.ext_to_ring** 是 Mathlib 中的一个定理，位于命名空间 `Bialgebra`。
形式化陈述：ext_to_ring (f g : A ->ₐc[R] R) : f = g
参数：f g : A ->ₐc[R] R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem ext_to_ring (f g : A →ₐc[R] R) : f = g := Subsingleton.elim _ _

end Bialgebra

