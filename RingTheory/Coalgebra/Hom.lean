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

/-- Given `R`-modules `A, B` with comultiplication maps `Δ_A, Δ_B` and counit maps
`ε_A, ε_B`, an `R`-coalgebra homomorphism `A →ₗc[R] B` is an `R`-linear map `f` such that
`ε_B ∘ f = ε_A` and `(f ⊗ f) ∘ Δ_A = Δ_B ∘ f`. -/
/-
**CoalgHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (A : Type u_2) →     (B : Type u_3) →       [inst : Com
mSemiring R] →         [inst_1 : AddCommMonoid A] →           [inst_2 : _root_.M
odule R A] →             [inst_3 : AddCommMonoid B] →               [inst_4 : _r
oot_.Module R B] → [CoalgebraStruct R A] → [CoalgebraStruct R B] → Type (max u_2
 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `R`-modules `A, B` with comultiplication maps `Δ_A, Δ_B` and counit maps
`ε_A, ε_B`, an `R`-coalgebra homomorphism `A →ₗc[R] B` is an `R`-linear map `f` 
such that
`ε_B ∘ f = ε_A` and `(f ⊗ f) ∘ Δ_A = Δ_B ∘ f`.
-/
structure CoalgHom (R A B : Type*) [CommSemiring R]
    [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A →ₗ[R] B where
  counit_comp : counit ∘ₗ toLinearMap = counit
  map_comp_comul : TensorProduct.map toLinearMap toLinearMap ∘ₗ comul = comul ∘ₗ toLinearMap

@[inherit_doc CoalgHom]
infixr:25 " →ₗc " => CoalgHom _

@[inherit_doc]
notation:25 A " →ₗc[" R "] " B => CoalgHom R A B

/-- `CoalgHomClass F R A B` asserts `F` is a type of bundled coalgebra homomorphisms
from `A` to `B`. -/
/-
**CoalgHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (R : outParam (Type u_2)) →     (A : outParam (Type u_3
)) →       (B : outParam (Type u_4)) →         [inst : CommSemiring R] →        
   [inst_1 : AddCommMonoid A] →             [inst_2 : _root_.Module R A] →      
         [inst_3 : AddCommMonoid B] →                 [inst_4 : _root_.Module R 
B] → [CoalgebraStruct R A] → [CoalgebraStruct R B] → [FunLike F A B] → Prop
参数：Type u_2；Type u_3；Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CoalgHomClass F R A B` asserts `F` is a type of bundled coalgebra homomorphisms
from `A` to `B`.
-/
class CoalgHomClass (F : Type*) (R A B : outParam Type*)
    [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B] : Prop
    extends SemilinearMapClass F (RingHom.id R) A B where
  counit_comp : ∀ f : F, counit ∘ₗ (f : A →ₗ[R] B) = counit
  map_comp_comul : ∀ f : F, TensorProduct.map (f : A →ₗ[R] B)
    (f : A →ₗ[R] B) ∘ₗ comul = comul ∘ₗ (f : A →ₗ[R] B)

attribute [simp] CoalgHomClass.counit_comp CoalgHomClass.map_comp_comul

namespace CoalgHomClass

variable {R A B F : Type*} [CommSemiring R]
  [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B]
  [CoalgHomClass F R A B]

/-- Turn an element of a type `F` satisfying `CoalgHomClass F R A B` into an actual
`CoalgHom`. This is declared as the default coercion from `F` to `A →ₗc[R] B`. -/
@[coe]
/-
**CoalgHomClass.toCoalgHom** 是 Mathlib 中的一个定义，位于命名空间 `CoalgHomClass`。
形式化陈述：toCoalgHom (f : F) : A ->ₗc[R] B
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
· 使用定理 `CoalgHomClass.counit_comp`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A
 : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {ins
t_1 : AddCommMo…
· 使用定理 `CoalgHomClass.map_comp_comul`：∀ {F : Type u_1} {R : outParam (Type u_2)}
 {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {
inst_1 : AddCommMo…

--- 原说明 ---
Turn an element of a type `F` satisfying `CoalgHomClass F R A B` into an actual
`CoalgHom`. This is declared as the default coercion from `F` to `A →ₗc[R] B`.
-/
def toCoalgHom (f : F) : A →ₗc[R] B :=
  { (f : A →ₗ[R] B) with
    toFun := f
    counit_comp := CoalgHomClass.counit_comp f
    map_comp_comul := CoalgHomClass.map_comp_comul f }
/-
**CoalgHomClass.instCoeToCoalgHom** 是 Mathlib 中的一个实例，位于命名空间 `CoalgHomClass`。
形式化陈述：instCoeToCoalgHom : CoeHead F (A ->ₗc[R] B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoeToCoalgHom : CoeHead F (A →ₗc[R] B) :=
  ⟨CoalgHomClass.toCoalgHom⟩

@[simp]
/-
**CoalgHomClass.counit_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHomClass`。
形式化陈述：counit_comp_apply (f : F) (x : A) : counit (f x) = counit (R
参数：f : F；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
· 使用定理 `CoalgHomClass.counit_comp`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A
 : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {ins
t_1 : AddCommMo…
-/
theorem counit_comp_apply (f : F) (x : A) : counit (f x) = counit (R := R) x :=
  LinearMap.congr_fun (counit_comp f) _

@[simp]
/-
**CoalgHomClass.map_comp_comul_apply** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHomClass`。
形式化陈述：map_comp_comul_apply (f : F) (x : A) : TensorProduct.map f f (σ₁₂
参数：f : F；x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
· 使用定理 `CoalgHomClass.map_comp_comul`：∀ {F : Type u_1} {R : outParam (Type u_2)}
 {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {
inst_1 : AddCommMo…
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

/-
**CoalgHom.funLike** 是 Mathlib 中的一个实例，位于命名空间 `CoalgHom`。
形式化陈述：funLike : FunLike (A ->ₗc[R] B) A B where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (A →ₗc[R] B) A B where
  coe f := f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
    rcases g with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
    congr
/-
**CoalgHom.coalgHomClass** 是 Mathlib 中的一个实例，位于命名空间 `CoalgHom`。
形式化陈述：coalgHomClass : CoalgHomClass (A ->ₗc[R] B) R A B where map_add
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
-/
instance coalgHomClass : CoalgHomClass (A →ₗc[R] B) R A B where
  map_add := fun f => f.map_add'
  map_smulₛₗ := fun f => f.map_smul'
  counit_comp := fun f => f.counit_comp
  map_comp_comul := fun f => f.map_comp_comul

/-- See Note [custom simps projection] -/
/-
**CoalgHom.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `CoalgHom.Simps`。
形式化陈述：{R : Type u_6} →   {α : Type u_7} →     {β : Type u_8} →       [inst : Com
mSemiring R] →         [inst_1 : AddCommMonoid α] →           [inst_2 : _root_.M
odule R α] →             [inst_3 : AddCommMonoid β] →               [inst_4 : _r
oot_.Module R β] →                 [inst_5 : CoalgebraStruct R α] → [inst_6 : Co
algebraStruct R β] → (α →ₗc[R] β) → α → β
参数：α →ₗc[R] β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.apply {R α β : Type*} [CommSemiring R]
    [AddCommMonoid α] [Module R α] [AddCommMonoid β]
    [Module R β] [CoalgebraStruct R α] [CoalgebraStruct R β]
    (f : α →ₗc[R] β) : α → β := f

initialize_simps_projections CoalgHom (toFun → apply)

@[simp]
/-
**CoalgHom.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommSemiring R] [in
st_1 : AddCommMonoid A]   [inst_2 : _root_.Module R A] [inst_3 : AddCommMonoid B
] [inst_4 : _root_.Module R B] [inst_5 : CoalgebraStruct R A]   [inst_6 : Coalge
braStruct R B] {F : Type u_6} [inst_7 : FunLike F A B] [inst_8 : CoalgHomClass F
 R A B] (f : F),   ⇑↑f = ⇑f
参数：f : F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_coe {F : Type*} [FunLike F A B] [CoalgHomClass F R A B] (f : F) :
    ⇑(f : A →ₗc[R] B) = f :=
  rfl

@[simp]
/-
**CoalgHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：coe_mk {f : A ->ₗ[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A ->ₗc[R] B) : A -> B) = f
参数：h h₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk {f : A →ₗ[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A →ₗc[R] B) : A → B) = f :=
  rfl

@[norm_cast]
/-
**CoalgHom.coe_mks** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：coe_mks {f : A -> B} (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A ->ₗc[R]
 B) = f
参数：h₁ h₂ h₃ h₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mks {f : A → B} (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A →ₗc[R] B) = f :=
  rfl

@[simp, norm_cast]
/-
**CoalgHom.coe_linearMap_mk** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：coe_linearMap_mk {f : A ->ₗ[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A ->ₗc[R] B) : A
 ->ₗ[R] B) = f
参数：h h₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
-/
theorem coe_linearMap_mk {f : A →ₗ[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A →ₗc[R] B) : A →ₗ[R] B) = f :=
  rfl

@[simp]
/-
**CoalgHom.toLinearMap_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：toLinearMap_eq_coe (f : A ->ₗc[R] B) : f.toLinearMap = f
参数：f : A ->ₗc[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_eq_coe (f : A →ₗc[R] B) : f.toLinearMap = f :=
  rfl

@[simp, norm_cast]
/-
**CoalgHom.coe_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：coe_toLinearMap (f : A ->ₗc[R] B) : ⇑(f : A ->ₗ[R] B) = f
参数：f : A ->ₗc[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
-/
theorem coe_toLinearMap (f : A →ₗc[R] B) : ⇑(f : A →ₗ[R] B) = f :=
  rfl

@[norm_cast]
/-
**CoalgHom.coe_toAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：coe_toAddMonoidHom (f : A ->ₗc[R] B) : ⇑(f : A ->+ B) = f
参数：f : A ->ₗc[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
-/
theorem coe_toAddMonoidHom (f : A →ₗc[R] B) : ⇑(f : A →+ B) = f :=
  rfl
/-
**CoalgHom.coe_fn_injective** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：coe_fn_injective : @Function.Injective (A ->ₗc[R] B) (A -> B) (↑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_fn_injective : @Function.Injective (A →ₗc[R] B) (A → B) (↑) :=
  DFunLike.coe_injective
/-
**CoalgHom.coe_fn_inj** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：coe_fn_inj {φ₁ φ₂ : A ->ₗc[R] B} : (φ₁ : A -> B) = φ₂ ↔ φ₁ = φ₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_fn_eq`：coe_fn_eq {f g : F} : (f : forall a : α, β a) = (g :
 forall a : α, β a) ↔ f = g
-/
theorem coe_fn_inj {φ₁ φ₂ : A →ₗc[R] B} : (φ₁ : A → B) = φ₂ ↔ φ₁ = φ₂ :=
  DFunLike.coe_fn_eq
/-
**CoalgHom.coe_linearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：coe_linearMap_injective : Function.Injective ((↑) : (A ->ₗc[R] B) -> A ->ₗ
[R] B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
· 使用定理 `CoalgHom.coe_fn_injective`：coe_fn_injective : @Function.Injective (A ->ₗ
c[R] B) (A -> B) (↑)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem coe_linearMap_injective : Function.Injective ((↑) : (A →ₗc[R] B) → A →ₗ[R] B) :=
  fun φ₁ φ₂ H => coe_fn_injective <|
    show ((φ₁ : A →ₗ[R] B) : A → B) = ((φ₂ : A →ₗ[R] B) : A → B) from congr_arg _ H
/-
**CoalgHom.coe_addMonoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：coe_addMonoidHom_injective : Function.Injective ((↑) : (A ->ₗc[R] B) -> A 
->+ B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearMap.toAddMonoidHom_injective`：toAddMonoidHom_injective : Function.
Injective (toAddMonoidHom : (M ->ₛₗ[σ] M₃) -> M ->+ M₃)
· 使用定理 `CoalgHom.coe_linearMap_injective`：coe_linearMap_injective : Function.Inj
ective ((↑) : (A ->ₗc[R] B) -> A ->ₗ[R] B)
-/
theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (A →ₗc[R] B) → A →+ B) :=
  LinearMap.toAddMonoidHom_injective.comp coe_linearMap_injective
/-
**CoalgHom.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommSemiring R] [in
st_1 : AddCommMonoid A]   [inst_2 : _root_.Module R A] [inst_3 : AddCommMonoid B
] [inst_4 : _root_.Module R B] [inst_5 : CoalgebraStruct R A]   [inst_6 : Coalge
braStruct R B] {φ₁ φ₂ : A →ₗc[R] B}, φ₁ = φ₂ → ∀ (x : A), φ₁ x = φ₂ x
参数：x : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected theorem congr_fun {φ₁ φ₂ : A →ₗc[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
  DFunLike.congr_fun H x
/-
**CoalgHom.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommSemiring R] [in
st_1 : AddCommMonoid A]   [inst_2 : _root_.Module R A] [inst_3 : AddCommMonoid B
] [inst_4 : _root_.Module R B] [inst_5 : CoalgebraStruct R A]   [inst_6 : Coalge
braStruct R B] (φ : A →ₗc[R] B) {x y : A}, x = y → φ x = φ y
参数：φ : A →ₗc[R] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
-/
protected theorem congr_arg (φ : A →ₗc[R] B) {x y : A} (h : x = y) : φ x = φ y :=
  DFunLike.congr_arg φ h

@[ext]
/-
**CoalgHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：ext {φ₁ φ₂ : A ->ₗc[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = φ₂
参数：H : forall x, φ₁ x = φ₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {φ₁ φ₂ : A →ₗc[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
  DFunLike.ext _ _ H

@[ext high]
/-
**CoalgHom.ext_of_ring** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：ext_of_ring {f g : R ->ₗc[R] A} (h : f 1 = g 1) : f = g
参数：h : f 1 = g 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgHom.coe_linearMap_injective`：coe_linearMap_injective : Function.Inj
ective ((↑) : (A ->ₗc[R] B) -> A ->ₗ[R] B)
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
-/
theorem ext_of_ring {f g : R →ₗc[R] A} (h : f 1 = g 1) : f = g :=
  coe_linearMap_injective (by ext; assumption)

@[simp]
/-
**CoalgHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：mk_coe {f : A ->ₗc[R] B} (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A ->ₗc
[R] B) = f
参数：h₁ h₂ h₃ h₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgHom.ext`：ext {φ₁ φ₂ : A ->ₗc[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁
 = φ₂
-/
theorem mk_coe {f : A →ₗc[R] B} (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A →ₗc[R] B) = f :=
  ext fun _ => rfl

/-- Copy of a `CoalgHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
/-
**CoalgHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `CoalgHom`。
形式化陈述：{R : Type u_1} →   {A : Type u_2} →     {B : Type u_3} →       [inst : Com
mSemiring R] →         [inst_1 : AddCommMonoid A] →           [inst_2 : _root_.M
odule R A] →             [inst_3 : AddCommMonoid B] →               [inst_4 : _r
oot_.Module R B] →                 [inst_5 : CoalgebraStruct R A] →             
      [inst_6 : CoalgebraStruct R B] → (f : A →ₗc[R] B) → (f' : A → B) → f' = ⇑f
 → A →ₗc[R] B
参数：f : A →ₗc[R] B；f' : A → B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `CoalgHom` with a new `toFun` equal to the old one. Useful to fix defi
nitional
equalities.
-/
protected def copy (f : A →ₗc[R] B) (f' : A → B) (h : f' = ⇑f) : A →ₗc[R] B :=
  { toLinearMap := (f : A →ₗ[R] B).copy f' h
    counit_comp := by ext; simp_all
    map_comp_comul := by simp only [(f : A →ₗ[R] B).copy_eq f' h,
      CoalgHomClass.map_comp_comul] }

@[simp]
/-
**CoalgHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：coe_copy (f : A ->ₗc[R] B) (f' : A -> B) (h : f' = ⇑f) : ⇑(f.copy f' h) = 
f'
参数：f : A ->ₗc[R] B；f' : A -> B；h : f' = ⇑f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : A →ₗc[R] B) (f' : A → B) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**CoalgHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：copy_eq (f : A ->ₗc[R] B) (f' : A -> B) (h : f' = ⇑f) : f.copy f' h = f
参数：f : A ->ₗc[R] B；f' : A -> B；h : f' = ⇑f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : A →ₗc[R] B) (f' : A → B) (h : f' = ⇑f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (R A)

/-- Identity map as a `CoalgHom`. -/
/-
**CoalgHom.id** 是 Mathlib 中的一个定义，位于命名空间 `CoalgHom`。
形式化陈述：(R : Type u_1) →   (A : Type u_2) →     [inst : CommSemiring R] →       [i
nst_1 : AddCommMonoid A] → [inst_2 : _root_.Module R A] → [inst_3 : CoalgebraStr
uct R A] → A →ₗc[R] A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identity map as a `CoalgHom`.
-/
@[simps!] protected def id : A →ₗc[R] A :=
  { LinearMap.id with
    counit_comp := by ext; rfl
    map_comp_comul := by simp only [map_id, LinearMap.id_comp, LinearMap.comp_id] }

variable {R A}

@[simp, norm_cast]
/-
**CoalgHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：coe_id : ⇑(CoalgHom.id R A) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(CoalgHom.id R A) = id :=
  rfl

@[simp]
/-
**CoalgHom.id_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：id_toLinearMap : (CoalgHom.id R A : A ->ₗ[R] A) = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
-/
theorem id_toLinearMap : (CoalgHom.id R A : A →ₗ[R] A) = LinearMap.id := rfl

/-- Composition of coalgebra homomorphisms. -/
/-
**CoalgHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `CoalgHom`。
形式化陈述：{R : Type u_1} →   {A : Type u_2} →     {B : Type u_3} →       {C : Type u
_4} →         [inst : CommSemiring R] →           [inst_1 : AddCommMonoid A] →  
           [inst_2 : _root_.Module R A] →               [inst_3 : AddCommMonoid 
B] →                 [inst_4 : _root_.Module R B] →                   [inst_5 : 
AddCommMonoid C] →                     [inst_6 : _root_.Module R C] →           
            [inst_7 : CoalgebraStruct R A] →                         [inst_8 : C
oalgebraStruct R B] →                           [inst_9 : CoalgebraStruct R C] →
 (B →ₗc[R] C) → (A →ₗc[R] B) → A →ₗc[R] C
参数：B →ₗc[R] C；A →ₗc[R] B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of coalgebra homomorphisms.
-/
@[simps!] def comp (φ₁ : B →ₗc[R] C) (φ₂ : A →ₗc[R] B) : A →ₗc[R] C :=
  { (φ₁ : B →ₗ[R] C) ∘ₗ (φ₂ : A →ₗ[R] B) with
    counit_comp := by ext; simp
    map_comp_comul := by ext; simp [map_comp] }

@[simp]
/-
**CoalgHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：coe_comp (φ₁ : B ->ₗc[R] C) (φ₂ : A ->ₗc[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂
参数：φ₁ : B ->ₗc[R] C；φ₂ : A ->ₗc[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (φ₁ : B →ₗc[R] C) (φ₂ : A →ₗc[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ := rfl

@[simp]
/-
**CoalgHom.comp_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：comp_toLinearMap (φ₁ : B ->ₗc[R] C) (φ₂ : A ->ₗc[R] B) : φ₁.comp φ₂ = (φ₁ 
: B ->ₗ[R] C) ∘ₗ (φ₂ : A ->ₗ[R] B)
参数：φ₁ : B ->ₗc[R] C；φ₂ : A ->ₗc[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
-/
theorem comp_toLinearMap (φ₁ : B →ₗc[R] C) (φ₂ : A →ₗc[R] B) :
    φ₁.comp φ₂ = (φ₁ : B →ₗ[R] C) ∘ₗ (φ₂ : A →ₗ[R] B) := rfl

variable (φ : A →ₗc[R] B)

@[simp]
/-
**CoalgHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：comp_id : φ.comp (CoalgHom.id R A) = φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgHom.ext`：ext {φ₁ φ₂ : A ->ₗc[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁
 = φ₂
-/
theorem comp_id : φ.comp (CoalgHom.id R A) = φ :=
  ext fun _x => rfl

@[simp]
/-
**CoalgHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：id_comp : (CoalgHom.id R B).comp φ = φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgHom.ext`：ext {φ₁ φ₂ : A ->ₗc[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁
 = φ₂
-/
theorem id_comp : (CoalgHom.id R B).comp φ = φ :=
  ext fun _x => rfl
/-
**CoalgHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：comp_assoc (φ₁ : C ->ₗc[R] D) (φ₂ : B ->ₗc[R] C) (φ₃ : A ->ₗc[R] B) : (φ₁.
comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃)
参数：φ₁ : C ->ₗc[R] D；φ₂ : B ->ₗc[R] C；φ₃ : A ->ₗc[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgHom.ext`：ext {φ₁ φ₂ : A ->ₗc[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁
 = φ₂
-/
theorem comp_assoc (φ₁ : C →ₗc[R] D) (φ₂ : B →ₗc[R] C) (φ₃ : A →ₗc[R] B) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
  ext fun _x => rfl
/-
**CoalgHom.map_smul_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
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
**CoalgHom.End** 是 Mathlib 中的一个实例，位于命名空间 `CoalgHom`。
形式化陈述：End : Monoid (A ->ₗc[R] A) where mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance End : Monoid (A →ₗc[R] A) where
  mul := comp
  mul_assoc _ _ _ := rfl
  one := CoalgHom.id R A
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl

@[simp]
/-
**CoalgHom.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：one_apply (x : A) : (1 : A ->ₗc[R] A) x = x
参数：x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (x : A) : (1 : A →ₗc[R] A) x = x :=
  rfl

@[simp]
/-
**CoalgHom.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `CoalgHom`。
形式化陈述：mul_apply (φ ψ : A ->ₗc[R] A) (x : A) : (φ * ψ) x = φ (ψ x)
参数：φ ψ : A ->ₗc[R] A；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (φ ψ : A →ₗc[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
  rfl

end

end CoalgHom

namespace Coalgebra

variable (R : Type u) (A : Type v) (B : Type w) {ι : Type*}

variable [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
variable [Coalgebra R A] [Coalgebra R B]

/-- The counit of a coalgebra as a `CoalgHom`. -/
/-
**Coalgebra.counitCoalgHom** 是 Mathlib 中的一个定义，位于命名空间 `Coalgebra`。
形式化陈述：counitCoalgHom : A ->ₗc[R] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit of a coalgebra as a `CoalgHom`.
-/
noncomputable def counitCoalgHom : A →ₗc[R] R :=
  { counit with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext
      simp only [LinearMap.coe_comp, Function.comp_apply, CommSemiring.comul_apply,
        ← LinearMap.lTensor_comp_rTensor, rTensor_counit_comul, LinearMap.lTensor_tmul] }

@[simp]
/-
**Coalgebra.counitCoalgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra`。
形式化陈述：counitCoalgHom_apply (x : A) : counitCoalgHom R A x = counit x
参数：x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem counitCoalgHom_apply (x : A) :
    counitCoalgHom R A x = counit x := rfl

@[simp]
/-
**Coalgebra.counitCoalgHom_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra`。
形式化陈述：counitCoalgHom_toLinearMap : counitCoalgHom R A = counit (R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgHomClass.toSemilinearMapClass`：∀ {F : Type u_1} {R : outParam (Type
 u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring 
R}   {inst_1 : AddCommMo…
-/
theorem counitCoalgHom_toLinearMap :
    counitCoalgHom R A = counit (R := R) (A := A) := rfl

variable {R}
/-
**Coalgebra.subsingleton_to_ring** 是 Mathlib 中的一个实例，位于命名空间 `Coalgebra`。
形式化陈述：subsingleton_to_ring : Subsingleton (A ->ₗc[R] R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CoalgHom.ext`：ext {φ₁ φ₂ : A ->ₗc[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁
 = φ₂
· 使用定理 `CoalgHomClass.counit_comp_apply`：counit_comp_apply (f : F) (x : A) : cou
nit (f x) = counit (R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance subsingleton_to_ring : Subsingleton (A →ₗc[R] R) :=
  ⟨fun f g => CoalgHom.ext fun x => by
    have hf := CoalgHomClass.counit_comp_apply f x
    have hg := CoalgHomClass.counit_comp_apply g x
    simp_all only [CommSemiring.counit_apply]⟩

@[ext high]
/-
**Coalgebra.ext_to_ring** 是 Mathlib 中的一个定理，位于命名空间 `Coalgebra`。
形式化陈述：ext_to_ring (f g : A ->ₗc[R] R) : f = g
参数：f g : A ->ₗc[R] R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem ext_to_ring (f g : A →ₗc[R] R) : f = g := Subsingleton.elim _ _

variable {A B}
/--
If `φ : A → B` is a coalgebra map and `a = ∑ xᵢ ⊗ yᵢ`, then `φ a = ∑ φ xᵢ ⊗ φ yᵢ`
-/
@[simps]
/-
**Coalgebra.Repr.induced** 是 Mathlib 中的一个定义，位于命名空间 `Coalgebra.Repr`。
形式化陈述：{R : Type u} →   {A : Type v} →     {B : Type w} →       {ι : Type u_1} → 
        [inst : CommSemiring R] →           [inst_1 : AddCommMonoid A] →        
     [inst_2 : AddCommMonoid B] →               [inst_3 : _root_.Module R A] →  
               [inst_4 : _root_.Module R B] →                   [inst_5 : Coalge
bra R A] →                     [inst_6 : Coalgebra R B] →                       
{a : A} →                         Coalgebra.Repr R a ι →                        
   {F : Type u_2} →                             [inst_7 : FunLike F A B] → [Coal
gHomClass F R A B] → (φ : F) → Coalgebra.Repr R (φ a) ι
参数：φ : F；φ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `φ : A → B` is a coalgebra map and `a = ∑ xᵢ ⊗ yᵢ`, then `φ a = ∑ φ xᵢ ⊗ φ yᵢ
`
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

