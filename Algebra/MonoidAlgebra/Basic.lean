/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Algebra structure on monoid algebras

-/

@[expose] public noncomputable section

open Finset

open Finsupp hiding single mapDomain

variable {R S T A B C M N O : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

/-! #### Non-unital, non-associative algebra structure -/


section NonUnitalNonAssocAlgebra

variable (R) [Semiring R] [Mul M] [NonUnitalNonAssocSemiring A]

/-- A non-unital `R`-algebra homomorphism from `R[M]` is uniquely defined by its
values on the monomials `single a 1`. -/
@[to_additive (dont_translate := R) /--
A non-unital `R`-algebra homomorphism from `R[M]` is uniquely defined by its
values on the monomials `single a 1`. -/]
/-
**MonoidAlgebra.nonUnitalAlgHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：nonUnitalAlgHom_ext [DistribMulAction R A] {φ₁ φ₂ : R[M] ->ₙₐ[R] A} (h : f
orall x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂
参数：h : forall x, φ₁ (single x 1) = φ₂ (single x 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHom.to_distribMulActionHom_injective`：to_distribMulActionHom
_injective {f g : A ->ₛₙₐ[φ] B} (h : (f : A ->ₑ+[φ] B) = (g : A ->ₑ+[φ] B)) : f 
= g
· 使用定理 `MonoidAlgebra.distribMulActionHom_ext'`：distribMulActionHom_ext' {N : Ty
pe*} [Monoid R] [AddMonoid N] [DistribMulAction R N] [DistribMulAction R S] {f g
 : S[M] ->+[R] N} (h : foral…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `DistribMulActionHom.ext_ring`：DistribMulActionHom.ext_ring {f g : R ->ₑ+
[σ] N'} (h : f 1 = g 1) : f = g
-/
theorem nonUnitalAlgHom_ext [DistribMulAction R A] {φ₁ φ₂ : R[M] →ₙₐ[R] A}
    (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
  NonUnitalAlgHom.to_distribMulActionHom_injective <|
    MonoidAlgebra.distribMulActionHom_ext' fun a => DistribMulActionHom.ext_ring (h a)

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
/-
**MonoidAlgebra.nonUnitalAlgHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：nonUnitalAlgHom_ext' [DistribMulAction R A] {φ₁ φ₂ : R[M] ->ₙₐ[R] A} (h : 
φ₁.toMulHom.comp (ofMagma R M) = φ₂.toMulHom.comp (ofMagma R M)) : φ₁ = φ₂
参数：h : φ₁.toMulHom.comp (ofMagma R M) = φ₂.toMulHom.comp (ofMagma R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.nonUnitalAlgHom_ext`：nonUnitalAlgHom_ext [DistribMulAction
 R A] {φ₁ φ₂ : R[M] ->ₙₐ[R] A} (h : forall x, φ₁ (single x 1) = φ₂ (single x 1))
 : φ₁ = φ₂
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
See note [partially-applied ext lemmas].
-/
theorem nonUnitalAlgHom_ext' [DistribMulAction R A] {φ₁ φ₂ : R[M] →ₙₐ[R] A}
    (h : φ₁.toMulHom.comp (ofMagma R M) = φ₂.toMulHom.comp (ofMagma R M)) : φ₁ = φ₂ :=
  nonUnitalAlgHom_ext R <| DFunLike.congr_fun h

set_option backward.isDefEq.respectTransparency false in
/-- The functor `M ↦ R[M]`, from the category of magmas to the category of non-unital,
non-associative algebras over `R` is adjoint to the forgetful functor in the other direction. -/
@[simps apply_apply symm_apply]
/-
**MonoidAlgebra.liftMagma** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：liftMagma [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] : (M ->
ₙ* A) ≃ (R[M] ->ₙₐ[R] A) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `M ↦ R[M]`, from the category of magmas to the category of non-unita
l,
non-associative algebras over `R` is adjoint to the forgetful functor in the oth
er direction.
-/
def liftMagma [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    (M →ₙ* A) ≃ (R[M] →ₙₐ[R] A) where
  toFun f := {
    toAddMonoidHom :=
      (liftAddHom fun x ↦ (smulAddHom R A).flip (f x)).comp coeffAddEquiv.toAddMonoidHom
    map_smul' t' a := by simp [Finsupp.smul_sum, sum_smul_index', mul_smul]
    map_mul' a₁ a₂ := by
      simpa [mul_def, sum_sum_index, add_smul, Finsupp.mul_sum, Finsupp.sum_mul,
        smul_mul_smul_comm] using Finsupp.sum_comm ..
  }
  invFun F := F.toMulHom.comp (ofMagma R M)
  left_inv f := by ext; simp
  right_inv F := by ext; simp

end NonUnitalNonAssocAlgebra

/-! #### Algebra structure -/

section Algebra
variable [CommSemiring R] [Semiring A] [Algebra R A] [Monoid M] [Monoid N]

set_option backward.defeqAttrib.useBackward true in
/-- The instance `Algebra R A[M]` whenever we have `Algebra R A`.

In particular this provides the instance `Algebra R R[M]`. -/
@[to_additive (dont_translate := R A)
/-- The instance `Algebra R R[M]` whenever we have `Algebra R R`.

In particular this provides the instance `Algebra R R[M]`. -/]
/-
**MonoidAlgebra.algebra** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
形式化陈述：algebra : Algebra R A[M] where algebraMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebra : Algebra R A[M] where
  algebraMap := singleOneRingHom.comp (algebraMap R A)
  smul_def' r a := by ext; simp [coeff_single_one_mul, Algebra.smul_def]
  commutes' r f := by ext; simp [coeff_single_one_mul, coeff_mul_single_one, Algebra.commutes]

/-- `MonoidAlgebra.single 1` as an `AlgHom` -/
@[to_additive (dont_translate := R A) (attr := simps! apply)
/-- `AddMonoidAlgebra.single 0` as an `AlgHom` -/]
/-
**MonoidAlgebra.singleOneAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：singleOneAlgHom : A ->ₐ[R] A[M] where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def singleOneAlgHom : A →ₐ[R] A[M] where
  __ := singleOneRingHom
  commutes' r := by ext; simp; rfl

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.coe_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：coe_algebraMap : ⇑(algebraMap R A[M]) = single 1 ∘ algebraMap R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_algebraMap : ⇑(algebraMap R A[M]) = single 1 ∘ algebraMap R A := rfl
/-
**MonoidAlgebra.single_eq_algebraMap_mul_of** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlg
ebra`。
形式化陈述：single_eq_algebraMap_mul_of (m : M) (r : R) : single m r = algebraMap R R[
M] r * of R M m
参数：m : M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用引理 `MonoidAlgebra.single_mul_single`：single_mul_single (m₁ m₂ : M) (r₁ r₂ : 
R) : single m₁ r₁ * single m₂ r₂ = single (m₁ * m₂) (r₁ * r₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma single_eq_algebraMap_mul_of (m : M) (r : R) :
    single m r = algebraMap R R[M] r * of R M m := by simp
/-
**MonoidAlgebra.single_algebraMap_eq_algebraMap_mul_of** 是 Mathlib 中的一个定理，位于命名空间
 `MonoidAlgebra`。
形式化陈述：single_algebraMap_eq_algebraMap_mul_of (m : M) (r : R) : single m (algebra
Map R A r) = algebraMap R A[M] r * of A M m
参数：m : M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用引理 `MonoidAlgebra.single_mul_single`：single_mul_single (m₁ m₂ : M) (r₁ r₂ : 
R) : single m₁ r₁ * single m₂ r₂ = single (m₁ * m₂) (r₁ * r₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_algebraMap_eq_algebraMap_mul_of (m : M) (r : R) :
    single m (algebraMap R A r) = algebraMap R A[M] r * of A M m := by simp

@[to_additive]
/-
**MonoidAlgebra.isLocalHom_singleOneAlgHom** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlge
bra`。
形式化陈述：isLocalHom_singleOneAlgHom : IsLocalHom (singleOneAlgHom : A ->ₐ[R] A[M]) 
where map_nonunit
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHom.map_nonunit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} {
inst : Monoid R} {inst_1 : Monoid S} {inst_2 : FunLike F R S} {f : F}   [self : 
IsLocalHom f…
-/
instance isLocalHom_singleOneAlgHom : IsLocalHom (singleOneAlgHom : A →ₐ[R] A[M]) where
  map_nonunit := isLocalHom_singleOneRingHom.map_nonunit

@[to_additive (dont_translate := R)]
/-
**MonoidAlgebra.isLocalHom_algebraMap** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
形式化陈述：isLocalHom_algebraMap [IsLocalHom (algebraMap R A)] : IsLocalHom (algebraM
ap R A[M]) where map_nonunit _ hx
参数：algebraMap R A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.of_map`：IsUnit.of_map (f : F) [IsLocalHom f] (a : R) (h : IsUnit 
(f a)) : IsUnit a
· 使用定理 `IsLocalHom.map_nonunit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} {
inst : Monoid R} {inst_1 : Monoid S} {inst_2 : FunLike F R S} {f : F}   [self : 
IsLocalHom f…
-/
instance isLocalHom_algebraMap [IsLocalHom (algebraMap R A)] :
    IsLocalHom (algebraMap R A[M]) where
  map_nonunit _ hx := .of_map _ _ <| isLocalHom_singleOneAlgHom (R := R).map_nonunit _ hx

variable (R M) in
/-- The trivial monoid algebra is the base ring. -/
@[to_additive (dont_translate := R A)
/-- The trivial monoid algebra is the base ring. -/]
/-
**MonoidAlgebra.uniqueAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：uniqueAlgEquiv [Subsingleton M] : A[M] ≃ₐ[R] A where toRingEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def uniqueAlgEquiv [Subsingleton M] : A[M] ≃ₐ[R] A where
  toRingEquiv := uniqueRingEquiv _
  commutes' r := by simp

set_option backward.isDefEq.respectTransparency.types false in
variable (R M) in
@[to_additive (dont_translate := A) (attr := simp)]
/-
**MonoidAlgebra.uniqueAlgEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgeb
ra`。
形式化陈述：uniqueAlgEquiv_symm_apply [Subsingleton M] (a : A) : (uniqueAlgEquiv R M).
symm a = single 1 a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.uniqueRingEquiv_symm_apply`：uniqueRingEquiv_symm_apply [Su
bsingleton M] (r : R) : (uniqueRingEquiv M).symm r = single 1 r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uniqueAlgEquiv_symm_apply [Subsingleton M] (a : A) :
    (uniqueAlgEquiv R M).symm a = single 1 a := by ext; simp [uniqueAlgEquiv]

-- We want this lemma to fire before `uniqueAlgEquiv_symm_apply`.
@[to_additive (dont_translate := A) (attr := simp↓ high)]
/-
**MonoidAlgebra.coeff_uniqueAlgEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgeb
ra`。
形式化陈述：coeff_uniqueAlgEquiv_symm [Subsingleton M] (a : A) (m : M) : ((uniqueAlgEq
uiv R M).symm a).coeff m = a
参数：a : A；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MonoidAlgebra.uniqueAlgEquiv_symm_apply`：uniqueAlgEquiv_symm_apply [Subs
ingleton M] (a : A) : (uniqueAlgEquiv R M).symm a = single 1 a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_uniqueAlgEquiv_symm [Subsingleton M] (a : A) (m : M) :
    ((uniqueAlgEquiv R M).symm a).coeff m = a := by simp [Subsingleton.elim m 1]

variable (R M) in
@[to_additive (attr := simp)]
/-
**MonoidAlgebra.toRingEquiv_uniqueAlgEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlge
bra`。
形式化陈述：toRingEquiv_uniqueAlgEquiv [Unique M] : RingEquivClass.toRingEquiv (unique
AlgEquiv R (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma toRingEquiv_uniqueAlgEquiv [Unique M] :
    RingEquivClass.toRingEquiv (uniqueAlgEquiv R (A := A) M) =
      uniqueRingEquiv (R := A) M := rfl

variable (R M) in
@[to_additive (attr := simp)]
/-
**MonoidAlgebra.toRingEquiv_symm_uniqueAlgEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Monoi
dAlgebra`。
形式化陈述：toRingEquiv_symm_uniqueAlgEquiv [Unique M] : RingEquivClass.toRingEquiv (u
niqueAlgEquiv R (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma toRingEquiv_symm_uniqueAlgEquiv [Unique M] :
    RingEquivClass.toRingEquiv (uniqueAlgEquiv R (A := A) M).symm =
      (uniqueRingEquiv (R := A) M).symm := rfl

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-- A product monoid algebra is a nested monoid algebra. -/
@[to_additive (dont_translate := R A)
/-- A product monoid algebra is a nested monoid algebra. -/]
/-
**MonoidAlgebra.curryAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：curryAlgEquiv : A[M × N] ≃ₐ[R] A[N][M] where toRingEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def curryAlgEquiv : A[M × N] ≃ₐ[R] A[N][M] where
  toRingEquiv := curryRingEquiv
  commutes' r := by
    ext
    simp [curryRingEquiv, curryAddEquiv, algebraMap, algebraMap, Algebra.algebraMap,
      singleOneRingHom, singleAddHom, curryAddEquiv, ← ofCoeff_single]

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.curryAlgEquiv_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：curryAlgEquiv_single (m : M) (n : N) (a : A) : curryAlgEquiv R (single (m,
 n) a) = single m (single n a)
参数：m : M；n : N；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.curryRingEquiv_single`：curryRingEquiv_single (m : M) (n : 
N) (r : R) : curryRingEquiv (single (m, n) r) = single m (single n r)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma curryAlgEquiv_single (m : M) (n : N) (a : A) :
    curryAlgEquiv R (single (m, n) a) = single m (single n a) := by simp [curryAlgEquiv]

set_option backward.isDefEq.respectTransparency.types false in
@[to_additive (attr := simp)]
/-
**MonoidAlgebra.curryAlgEquiv_symm_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgeb
ra`。
形式化陈述：curryAlgEquiv_symm_single (m : M) (n : N) (a : A) : (curryAlgEquiv R).symm
 (single m <| single n a) = (single (m, n) a)
参数：m : M；n : N；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.curryRingEquiv_symm_single`：curryRingEquiv_symm_single (m 
: M) (n : N) (r : R) : curryRingEquiv.symm (single m <| single n r) = (single (m
, n) r)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma curryAlgEquiv_symm_single (m : M) (n : N) (a : A) :
    (curryAlgEquiv R).symm (single m <| single n a) = (single (m, n) a) := by
  simp [curryAlgEquiv]

end Algebra

variable (R A) in
/-- If `f : M → N` is a homomorphism between two magmas, then `MonoidAlgebra.mapDomain f`
is a non-unital algebra homomorphism between their magma algebras. -/
@[to_additive (dont_translate := R A) (attr := simps apply)
/-- If `f : M → N` is a homomorphism between two additive magmas,
then `AddMonoidAlgebra.mapDomain f` is a non-unital algebra homomorphism
between their additive magma algebras. -/]
/-
**MonoidAlgebra.mapDomainNonUnitalAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebr
a`。
形式化陈述：mapDomainNonUnitalAlgHom [CommSemiring R] [Semiring A] [Algebra R A] [Mul 
M] [Mul N] (f : M ->ₙ* N) : A[M] ->ₙₐ[R] A[N] where __
参数：f : M ->ₙ* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapDomainNonUnitalAlgHom [CommSemiring R] [Semiring A] [Algebra R A]
    [Mul M] [Mul N] (f : M →ₙ* N) : A[M] →ₙₐ[R] A[N] where
  __ := mapDomainNonUnitalRingHom A f
  map_mul' := mapDomain_mul f
  map_smul' _ _ := mapDomain_smul ..

variable (A) in
@[to_additive]
/-
**MonoidAlgebra.mapDomain_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomain_algebraMap {F : Type*} [CommSemiring R] [Semiring A] [Algebra R 
A] [Monoid M] [Monoid N] [FunLike F M N] [MonoidHomClass F M N] (f : F) (r : R) 
: mapDomain f (algebraMap R A[M] r) = algebraMap R A[N] r
参数：f : F；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.mapDomain_single`：mapDomain_single : mapDomain f (single a
 r) = single (f a) r
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapDomain_algebraMap {F : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Monoid M] [Monoid N] [FunLike F M N] [MonoidHomClass F M N] (f : F) (r : R) :
    mapDomain f (algebraMap R A[M] r) = algebraMap R A[N] r := by
  simp only [coe_algebraMap, mapDomain_single, map_one, (· ∘ ·)]

section lift
variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

/-- `liftNCRingHom` as an `AlgHom`, for when `f` is an `AlgHom` -/
/-
**MonoidAlgebra.liftNCAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：liftNCAlgHom (f : A ->ₐ[R] B) (g : M ->* B) (h_comm : forall x y, Commute 
(f x) (g y)) : A[M] ->ₐ[R] B
参数：f : A ->ₐ[R] B；g : M ->* B；h_comm : forall x y, Commute (f x) (g y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`liftNCRingHom` as an `AlgHom`, for when `f` is an `AlgHom`
-/
def liftNCAlgHom (f : A →ₐ[R] B) (g : M →* B) (h_comm : ∀ x y, Commute (f x) (g y)) :
    A[M] →ₐ[R] B :=
  { liftNCRingHom (f : A →+* B) g h_comm with
    commutes' := by simp [liftNCRingHom] }
/-
**MonoidAlgebra.coe_liftNCAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：∀ {R : Type u_1} {A : Type u_4} {B : Type u_5} {M : Type u_7} [inst : Comm
Semiring R] [inst_1 : Semiring A]   [inst_2 : Semiring B] [inst_3 : Algebra R A]
 [inst_4 : Algebra R B] [inst_5 : Monoid M] (f : A →ₐ[R] B) (g : M →* B)   (h_co
mm : ∀ (x : A) (y : M), Commute (f x) (g y)),   ⇑(MonoidAlgebra.liftNCAlgHom f g
 h_comm) = ⇑(MonoidAlgebra.liftNC ↑f ⇑g)
参数：f : A →ₐ[R] B；g : M →* B；h_comm : ∀ (x : A) (y : M), Commute (f x) (g y)；Mono
idAlgebra.liftNCAlgHom f g h_comm；MonoidAlgebra.liftNC ↑f ⇑g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_liftNCAlgHom (f : A →ₐ[R] B) (g : M →* B) (h_comm) :
    ⇑(liftNCAlgHom f g h_comm) = liftNC f g := rfl

-- The priority must be `high`.
/-- A `R`-algebra homomorphism from `A[M]` is uniquely defined by its
values on the functions `single m 1` and `single 1 a`.

See note [partially-applied ext lemmas]. Note that the first assumption isn't written as an
equality of `MonoidHom`s because `of` doesn't additivise. -/
@[to_additive (dont_translate := R A B) (attr := ext high) /--
A `R`-algebra homomorphism from `A[M]` is uniquely defined by its
values on the functions `single m 1` and `single 1 a`.

See note [partially-applied ext lemmas]. Note that the first assumption isn't written as an
equality of `AddMonoidHom`s because `of` doesn't multiplicativise. -/]
/-
**MonoidAlgebra.algHom_ext** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：algHom_ext ⦃φ₁ φ₂ : A[M] ->ₐ[R] B⦄ (single_one_right : forall m, φ₁ (singl
e m 1) = φ₂ (single m 1)) (single_one_left : φ₁.comp singleOneAlgHom = φ₂.comp s
ingleOneAlgHom) : φ₁ = φ₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用引理 `MonoidAlgebra.induction_linear`：induction_linear {motive : R[M] -> Prop}
 (x : R[M]) (zero : motive 0) (add : forall x y : R[M], motive x -> motive y -> 
motive (x + y)) (sin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MonoidAlgebra.singleOneAlgHom_apply`：∀ {R : Type u_1} {A : Type u_4} {M 
: Type u_7} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]
   [inst_3 : Monoid M] (a…
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用引理 `MonoidAlgebra.single_mul_single`：single_mul_single (m₁ m₂ : M) (r₁ r₂ : 
R) : single m₁ r₁ * single m₂ r₂ = single (m₁ * m₂) (r₁ * r₂)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma algHom_ext ⦃φ₁ φ₂ : A[M] →ₐ[R] B⦄ (single_one_right : ∀ m, φ₁ (single m 1) = φ₂ (single m 1))
    (single_one_left : φ₁.comp singleOneAlgHom = φ₂.comp singleOneAlgHom) :
    φ₁ = φ₂ := by
  ext x
  induction x using induction_linear with
  | zero => simp
  | add => simp_all
  | single m a => simpa [← map_mul] using congr($(single_one_right m) * $single_one_left a)

/-- Version of `algHom_ext` where both assumptions are written as equalities of bundled homs. -/
/-
**MonoidAlgebra.algHom_ext'** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：algHom_ext' ⦃φ₁ φ₂ : A[M] ->ₐ[R] B⦄ (single_one_right : (φ₁ : A[M] ->* B).
comp (of A M) = (φ₂ : A[M] ->* B).comp (of A M)) (single_one_left : φ₁.comp sing
leOneAlgHom = φ₂.comp singleOneAlgHom) : φ₁ = φ₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `MonoidAlgebra.algHom_ext`：algHom_ext ⦃φ₁ φ₂ : A[M] ->ₐ[R] B⦄ (single_one
_right : forall m, φ₁ (single m 1) = φ₂ (single m 1)) (single_one_left : φ₁.comp
 singleOneAlgH…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Version of `algHom_ext` where both assumptions are written as equalities of bund
led homs.
-/
lemma algHom_ext' ⦃φ₁ φ₂ : A[M] →ₐ[R] B⦄
    (single_one_right : (φ₁ : A[M] →* B).comp (of A M) = (φ₂ : A[M] →* B).comp (of A M))
    (single_one_left : φ₁.comp singleOneAlgHom = φ₂.comp singleOneAlgHom) : φ₁ = φ₂ :=
  algHom_ext (congr($single_one_right ·)) single_one_left

set_option backward.isDefEq.respectTransparency false in
variable (R A M) in
/-- Any monoid homomorphism `M →* A` can be lifted to an algebra homomorphism `R[M] →ₐ[R] A`. -/
/-
**MonoidAlgebra.lift** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：lift : (M ->* A) ≃ (R[M] ->ₐ[R] A) where toFun F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any monoid homomorphism `M →* A` can be lifted to an algebra homomorphism `R[M] 
→ₐ[R] A`.
-/
def lift : (M →* A) ≃ (R[M] →ₐ[R] A) where
  toFun F := liftNCAlgHom (Algebra.ofId R A) F fun _ _ ↦ Algebra.commutes _ _
  invFun f := (f : R[M] →* A).comp (of R M)
  left_inv f := by ext; simp
  right_inv F := by ext; simp
/-
**MonoidAlgebra.lift_apply'** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：lift_apply' (F : M ->* A) (f : R[M]) : lift R A M F f = f.coeff.sum fun a 
b => algebraMap R A b * F a
参数：F : M ->* A；f : R[M]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_apply' (F : M →* A) (f : R[M]) :
    lift R A M F f = f.coeff.sum fun a b => algebraMap R A b * F a :=
  rfl
/-
**MonoidAlgebra.lift_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：lift_apply (F : M ->* A) (f : R[M]) : lift R A M F f = f.coeff.sum fun a b
 => b • F a
参数：F : M ->* A；f : R[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_apply (F : M →* A) (f : R[M]) :
    lift R A M F f = f.coeff.sum fun a b => b • F a := by simp only [lift_apply', Algebra.smul_def]
/-
**MonoidAlgebra.lift_def** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：lift_def (F : M ->* A) : ⇑(lift R A M F) = liftNC (algebraMap R A) F
参数：F : M ->* A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_def (F : M →* A) : ⇑(lift R A M F) = liftNC (algebraMap R A) F := rfl

@[simp]
/-
**MonoidAlgebra.lift_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：lift_symm_apply (F : R[M] ->ₐ[R] A) (m : M) : (lift R A M).symm F m = F (s
ingle m 1)
参数：F : R[M] ->ₐ[R] A；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem lift_symm_apply (F : R[M] →ₐ[R] A) (m : M) : (lift R A M).symm F m = F (single m 1) := rfl

@[simp]
/-
**MonoidAlgebra.lift_single** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：lift_single (F : M ->* A) (a b) : lift R A M F (single a b) = b • F a
参数：F : M ->* A；a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.lift_def`：lift_def (F : M ->* A) : ⇑(lift R A M F) = liftN
C (algebraMap R A) F
· 使用定理 `MonoidAlgebra.liftNC_single`：liftNC_single (f : k ->+ R) (g : G -> R) (a
 : G) (b : k) : liftNC f g (single a b) = f b * g a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `AddMonoidHom.coe_coe`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [in
st : AddZero M] [inst_1 : AddZero N] [inst_2 : FunLike F M N]   [inst_3 : AddMon
oidHomClas…
-/
theorem lift_single (F : M →* A) (a b) : lift R A M F (single a b) = b • F a := by
  rw [lift_def, liftNC_single, Algebra.smul_def, AddMonoidHom.coe_coe]
/-
**MonoidAlgebra.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：lift_of (F : M ->* A) (m : M) : lift R A M F (of R M m) = F m
参数：F : M ->* A；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用定理 `MonoidAlgebra.lift_single`：lift_single (F : M ->* A) (a b) : lift R A M 
F (single a b) = b • F a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_of (F : M →* A) (m : M) : lift R A M F (of R M m) = F m := by simp
/-
**MonoidAlgebra.lift_unique'** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：lift_unique' (F : R[M] ->ₐ[R] A) : F = lift R A M ((F : R[M] ->* A).comp (
of R M))
参数：F : R[M] ->ₐ[R] A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem lift_unique' (F : R[M] →ₐ[R] A) : F = lift R A M ((F : R[M] →* A).comp (of R M)) :=
  ((lift R A M).apply_symm_apply F).symm

/-- Decomposition of a `R`-algebra homomorphism from `R[M]` by
its values on `F (single a 1)`. -/
/-
**MonoidAlgebra.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：lift_unique (F : R[M] ->ₐ[R] A) (f : R[M]) : F f = f.coeff.sum fun a b => 
b • F (single a 1)
参数：F : R[M] ->ₐ[R] A；f : R[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.lift_unique'`：lift_unique' (F : R[M] ->ₐ[R] A) : F = lift 
R A M ((F : R[M] ->* A).comp (of R M))
· 使用定理 `MonoidAlgebra.lift_apply`：lift_apply (F : M ->* A) (f : R[M]) : lift R A
 M F f = f.coeff.sum fun a b => b • F a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1

--- 原说明 ---
Decomposition of a `R`-algebra homomorphism from `R[M]` by
its values on `F (single a 1)`.
-/
theorem lift_unique (F : R[M] →ₐ[R] A) (f : R[M]) :
    F f = f.coeff.sum fun a b => b • F (single a 1) := by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]
/-
**MonoidAlgebra.lift_mapRingHom_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlge
bra`。
形式化陈述：lift_mapRingHom_algebraMap [CommSemiring S] [Algebra S A] [Algebra R S] [I
sScalarTower R S A] (f : M ->* A) (x : R[M]) : lift _ _ _ f (mapRingHom _ (algeb
raMap R S) x) = lift _ _ _ f x
参数：f : M ->* A；x : R[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.induction`：induction {motive : R[M] -> Prop} (x : R[M]) (z
ero : motive 0) (single_add : forall m r x, m ∉ x.coeff.support -> r != 0 -> mot
ive x -> moti…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MonoidAlgebra.mapRingHom_single`：mapRingHom_single (f : R ->+* S) (a : M
) (b : R) : mapRingHom M f (single a b) = single a (f b)
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MonoidAlgebra.lift_single`：lift_single (F : M ->* A) (a b) : lift R A M 
F (single a b) = b • F a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
-/
theorem lift_mapRingHom_algebraMap [CommSemiring S] [Algebra S A]
    [Algebra R S] [IsScalarTower R S A]
    (f : M →* A) (x : R[M]) :
    lift _ _ _ f (mapRingHom _ (algebraMap R S) x) = lift _ _ _ f x := by
  induction x using induction with
  | zero => simp
  | single_add a b f _ _ ih => simp [ih]

@[deprecated (since := "2026-06-18")]
alias lift_mapRangeRingHom_algebraMap := lift_mapRingHom_algebraMap

set_option backward.isDefEq.respectTransparency false in
variable (R A) in
/-- If `f : M → N` is a monoid homomorphism, then `MonoidAlgebra.mapDomain f` is an algebra
homomorphism between their monoid algebras. -/
@[to_additive (dont_translate := R A) (attr := simps! apply)
/-- If `f : M → N` is an additive monoid homomorphism, then `MonoidAlgebra.mapDomain f` is an
algebra homomorphism between their additive monoid algebras. -/]
/-
**MonoidAlgebra.mapDomainAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomainAlgHom (f : M ->* N) : A[M] ->ₐ[R] A[N] where toRingHom
参数：f : M ->* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapDomainAlgHom (f : M →* N) : A[M] →ₐ[R] A[N] where
  toRingHom := mapDomainRingHom A f
  commutes' := by simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := A) (attr := simp)]
/-
**MonoidAlgebra.mapDomainAlgHom_id** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomainAlgHom_id : mapDomainAlgHom R A (.id M) = .id R A[M]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.algHom_ext`：algHom_ext ⦃φ₁ φ₂ : A[M] ->ₐ[R] B⦄ (single_one
_right : forall m, φ₁ (single m 1) = φ₂ (single m 1)) (single_one_left : φ₁.comp
 singleOneAlgH…
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.mapDomainAlgHom_apply`：∀ (R : Type u_1) (A : Type u_4) {M 
: Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst
_2 : Algebra R A] [inst_3…
· 使用引理 `MonoidAlgebra.mapDomain_single`：mapDomain_single : mapDomain f (single a
 r) = single (f a) r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MonoidAlgebra.singleOneAlgHom_apply`：∀ {R : Type u_1} {A : Type u_4} {M 
: Type u_7} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]
   [inst_3 : Monoid M] (a…
-/
lemma mapDomainAlgHom_id : mapDomainAlgHom R A (.id M) = .id R A[M] := by ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := A) (attr := simp)]
/-
**MonoidAlgebra.mapDomainAlgHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomainAlgHom_comp (f : M ->* N) (g : N ->* O) : mapDomainAlgHom R A (g.
comp f) = (mapDomainAlgHom R A g).comp (mapDomainAlgHom R A f)
参数：f : M ->* N；g : N ->* O。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.algHom_ext`：algHom_ext ⦃φ₁ φ₂ : A[M] ->ₐ[R] B⦄ (single_one
_right : forall m, φ₁ (single m 1) = φ₂ (single m 1)) (single_one_left : φ₁.comp
 singleOneAlgH…
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidAlgebra.mapDomainAlgHom_apply`：∀ (R : Type u_1) (A : Type u_4) {M 
: Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst
_2 : Algebra R A] [inst_3…
· 使用引理 `MonoidAlgebra.mapDomain_single`：mapDomain_single : mapDomain f (single a
 r) = single (f a) r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `MonoidAlgebra.singleOneAlgHom_apply`：∀ {R : Type u_1} {A : Type u_4} {M 
: Type u_7} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]
   [inst_3 : Monoid M] (a…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
lemma mapDomainAlgHom_comp (f : M →* N) (g : N →* O) :
    mapDomainAlgHom R A (g.comp f) = (mapDomainAlgHom R A g).comp (mapDomainAlgHom R A f) := by
  ext <;> simp

variable (R A) in
/-- If `e : M ≃* N` is a multiplicative equivalence between two monoids, then
`MonoidAlgebra.domCongr e` is an algebra equivalence between their monoid algebras. -/
@[to_additive (dont_translate := A)
/-- If `e : M ≃+ N` is an additive equivalence between two additive monoids, then
`AddMonoidAlgebra.domCongr e` is an algebra equivalence between their additive monoid algebras. -/]
/-
**MonoidAlgebra.domCongr** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：domCongr (e : M ≃* N) : A[M] ≃ₐ[R] A[N] where toRingEquiv
参数：e : M ≃* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def domCongr (e : M ≃* N) : A[M] ≃ₐ[R] A[N] where
  toRingEquiv := mapDomainRingEquiv A e
  commutes' _ := by ext; simp

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.coeff_domCongr** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：coeff_domCongr (e : M ≃* N) (f : A[M]) (n : N) : (domCongr R A e f).coeff 
n = f.coeff (e.symm n)
参数：e : M ≃* N；f : A[M]；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.coeff_mapDomainRingEquiv`：coeff_mapDomainRingEquiv (e : M 
≃* N) (x : R[M]) : (mapDomainRingEquiv R e x).coeff = equivMapDomain e x.coeff
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_domCongr (e : M ≃* N) (f : A[M]) (n : N) :
    (domCongr R A e f).coeff n = f.coeff (e.symm n) := by simp [domCongr]

@[deprecated (since := "2026-06-18")] alias domCongr_apply := coeff_domCongr

@[to_additive]
/-
**MonoidAlgebra.domCongr_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：domCongr_toAlgHom (e : M ≃* N) : (domCongr R A e).toAlgHom = mapDomainAlgH
om R A e
参数：e : M ≃* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domCongr_toAlgHom (e : M ≃* N) : (domCongr R A e).toAlgHom = mapDomainAlgHom R A e := rfl

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/-
**MonoidAlgebra.domCongr_support** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：domCongr_support (e : M ≃* N) (x : A[M]) : (domCongr R A e x).coeff.suppor
t = x.coeff.support.map e
参数：e : M ≃* N；x : A[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `MonoidAlgebra.coeff_mapDomainRingEquiv`：coeff_mapDomainRingEquiv (e : M 
≃* N) (x : R[M]) : (mapDomainRingEquiv R e x).coeff = equivMapDomain e x.coeff
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma domCongr_support (e : M ≃* N) (x : A[M]) :
    (domCongr R A e x).coeff.support = x.coeff.support.map e := by simp [domCongr, equivMapDomain]

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.domCongr_single** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：domCongr_single (e : M ≃* N) (m : M) (a : A) : domCongr R A e (single m a)
 = single (e m) a
参数：e : M ≃* N；m : M；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.mapDomainRingEquiv_single`：mapDomainRingEquiv_single (e : 
M ≃* N) (r : R) (m : M) : mapDomainRingEquiv R e (single m r) = single (e m) r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem domCongr_single (e : M ≃* N) (m : M) (a : A) :
    domCongr R A e (single m a) = single (e m) a := by simp [domCongr]

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.domCongr_comp_lsingle** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：domCongr_comp_lsingle (e : M ≃* N) (m : M) : (domCongr R A e).toLinearMap 
∘ₗ lsingle m = lsingle (e m)
参数：e : M ≃* N；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.domCongr_single`：domCongr_single (e : M ≃* N) (m : M) (a :
 A) : domCongr R A e (single m a) = single (e m) a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma domCongr_comp_lsingle (e : M ≃* N) (m : M) :
    (domCongr R A e).toLinearMap ∘ₗ lsingle m = lsingle (e m) := by ext; simp

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.domCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：domCongr_refl : domCongr R A (.refl M) = .refl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.coeff_domCongr`：coeff_domCongr (e : M ≃* N) (f : A[M]) (n 
: N) : (domCongr R A e f).coeff n = f.coeff (e.symm n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem domCongr_refl : domCongr R A (.refl M) = .refl := by ext; simp

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.domCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：domCongr_symm (e : M ≃* N) : (domCongr R A e).symm = domCongr R A e.symm
参数：e : M ≃* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domCongr_symm (e : M ≃* N) : (domCongr R A e).symm = domCongr R A e.symm := rfl

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.trans_domCongr_domCongr** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra
`。
形式化陈述：trans_domCongr_domCongr (e : M ≃* N) (f : N ≃* O) : (domCongr R A e).trans
 (domCongr R A f) = domCongr R A (e.trans f)
参数：e : M ≃* N；f : N ≃* O。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.coeff_domCongr`：coeff_domCongr (e : M ≃* N) (f : A[M]) (n 
: N) : (domCongr R A e f).coeff n = f.coeff (e.symm n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trans_domCongr_domCongr (e : M ≃* N) (f : N ≃* O) :
    (domCongr R A e).trans (domCongr R A f) = domCongr R A (e.trans f) := by
  ext
  simp

/-- `MonoidAlgebra.domCongr` as a `MonoidHom` from `MulAut`. -/
@[simps]
/-
**MonoidAlgebra.domCongrAut** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：domCongrAut : MulAut M ->* A[M] ≃ₐ[R] A[M] where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MonoidAlgebra.domCongr` as a `MonoidHom` from `MulAut`.
-/
def domCongrAut : MulAut M →* A[M] ≃ₐ[R] A[M] where
  toFun := MonoidAlgebra.domCongr R A
  map_one' := by rw [MulAut.one_def, AlgEquiv.aut_one, domCongr_refl]
  map_mul' _ _ := by rw [MulAut.mul_def, AlgEquiv.aut_mul, trans_domCongr_domCongr]

variable (R) in
/-- Nested monoid algebras can be taken in an arbitrary order. -/
@[to_additive
/-- Nested monoid algebras can be taken in an arbitrary order. -/]
/-
**MonoidAlgebra.commAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：commAlgEquiv : A[M][N] ≃ₐ[R] A[N][M]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def commAlgEquiv : A[M][N] ≃ₐ[R] A[N][M] :=
  (curryAlgEquiv _).symm.trans <| .trans (domCongr _ _ <| .prodComm ..) (curryAlgEquiv _)

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.symm_commAlgEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：symm_commAlgEquiv : (commAlgEquiv R : A[M][N] ≃ₐ[R] A[N][M]).symm = commAl
gEquiv R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_commAlgEquiv : (commAlgEquiv R : A[M][N] ≃ₐ[R] A[N][M]).symm = commAlgEquiv R := rfl

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.commAlgEquiv_single_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlge
bra`。
形式化陈述：commAlgEquiv_single_single (m : M) (n : N) (a : A) : commAlgEquiv R (singl
e m <| single n a) = single n (single m a)
参数：m : M；n : N；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.commRingEquiv_single_single`：commRingEquiv_single_single (
m : M) (n : N) (r : R) : commRingEquiv (single m <| single n r) = single n (sing
le m r)
-/
lemma commAlgEquiv_single_single (m : M) (n : N) (a : A) :
    commAlgEquiv R (single m <| single n a) = single n (single m a) :=
  commRingEquiv_single_single ..

@[to_additive (dont_translate := A) (attr := simp)]
/-
**MonoidAlgebra.commAlgEquiv_single_one** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra
`。
形式化陈述：commAlgEquiv_single_one (m : M) : commAlgEquiv R (single m (1 : A[N])) = s
ingle 1 (single m 1)
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.commRingEquiv_single_one`：commRingEquiv_single_one (m : M)
 : commRingEquiv (single m (1 : R[N])) = single 1 (single m 1)
-/
lemma commAlgEquiv_single_one (m : M) :
    commAlgEquiv R (single m (1 : A[N])) = single 1 (single m 1) := commRingEquiv_single_one ..

-- We want this lemma to be tried before `commAlgEquiv_single_single`.
@[to_additive (dont_translate := A) (attr := simp high)]
/-
**MonoidAlgebra.commAlgEquiv_single_one_single** 是 Mathlib 中的一个引理，位于命名空间 `Monoid
Algebra`。
形式化陈述：commAlgEquiv_single_one_single (m : M) : commAlgEquiv R (single 1 <| singl
e m 1) = (single m (1 : A[N]))
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.commRingEquiv_single_one_single`：commRingEquiv_single_one_
single (m : M) : commRingEquiv (single 1 <| single m 1) = (single m (1 : R[N]))
-/
lemma commAlgEquiv_single_one_single (m : M) :
    commAlgEquiv R (single 1 <| single m 1) = (single m (1 : A[N])) :=
  commRingEquiv_single_one_single ..

end lift

section mapRange
variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Semiring C]
  [Algebra R A] [Algebra R B] [Algebra R C] [Monoid M] [Monoid N]

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapDomainRingHom_comp_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `Mono
idAlgebra`。
形式化陈述：mapDomainRingHom_comp_algebraMap (f : M ->* N) : (mapDomainRingHom A f).co
mp (algebraMap R A[M]) = algebraMap R A[N]
参数：f : M ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.mapDomainRingHom_apply`：∀ (R : Type u_3) {M : Type u_6} {N
 : Type u_7} [inst : Semiring R] [inst_1 : Monoid M] [inst_2 : Monoid N] (f : M 
→* N)   (x : MonoidAlgebra…
· 使用引理 `MonoidAlgebra.mapDomain_single`：mapDomain_single : mapDomain f (single a
 r) = single (f a) r
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomainRingHom_comp_algebraMap (f : M →* N) :
    (mapDomainRingHom A f).comp (algebraMap R A[M]) = algebraMap R A[N] := by ext; simp

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapRingHom_comp_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlge
bra`。
形式化陈述：mapRingHom_comp_algebraMap (f : R ->+* S) : (mapRingHom (M
参数：f : R ->+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用引理 `MonoidAlgebra.mapRingHom_single`：mapRingHom_single (f : R ->+* S) (a : M
) (b : R) : mapRingHom M f (single a b) = single a (f b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapRingHom_comp_algebraMap (f : R →+* S) :
    (mapRingHom (M := M) f).comp (algebraMap _ _) = (algebraMap _ _).comp f := by ext; simp

@[deprecated (since := "2026-06-18")]
alias mapRangeRingHom_comp_algebraMap := mapRingHom_comp_algebraMap

variable (M) in
/-- The algebra homomorphism of monoid algebras induced by a homomorphism of the base algebras. -/
@[to_additive
/-- The algebra homomorphism of additive monoid algebras induced by a homomorphism of the base
algebras. -/]
/-
**MonoidAlgebra.mapAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapAlgHom (f : A ->ₐ[R] B) : A[M] ->ₐ[R] B[M] where __
参数：f : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def mapAlgHom (f : A →ₐ[R] B) : A[M] →ₐ[R] B[M] where
  __ := mapRingHom M f
  commutes' := by simp

@[deprecated (since := "2026-06-18")] alias mapRangeAlgHom := mapAlgHom

variable (M) in
@[to_additive (attr := simp)]
/-
**MonoidAlgebra.toRingHom_mapAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：toRingHom_mapAlgHom (f : A ->ₐ[R] B) : mapAlgHom M f = mapRingHom M f.toRi
ngHom
参数：f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
lemma toRingHom_mapAlgHom (f : A →ₐ[R] B) :
    mapAlgHom M f = mapRingHom M f.toRingHom := rfl

@[deprecated (since := "2026-06-18")] alias toRingHom_mapRangeAlgHom := toRingHom_mapAlgHom

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.coeff_mapAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：coeff_mapAlgHom (f : A ->ₐ[R] B) (x : A[M]) (m : M) : (mapAlgHom M f x).co
eff m = f (x.coeff m)
参数：f : A ->ₐ[R] B；x : A[M]；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.coeff_mapRingHom`：coeff_mapRingHom (f : R ->+* S) (x : R[M
]) (m : M) : (mapRingHom M f x).coeff m = f (x.coeff m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_mapAlgHom (f : A →ₐ[R] B) (x : A[M]) (m : M) :
    (mapAlgHom M f x).coeff m = f (x.coeff m) := by simp [mapAlgHom]

@[deprecated (since := "2026-06-18")] alias mapAlgHom_apply := coeff_mapAlgHom
@[deprecated (since := "2026-06-18")] alias mapRangeAlgHom_apply := coeff_mapAlgHom

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapAlgHom_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapAlgHom_single (f : A ->ₐ[R] B) (m : M) (a : A) : mapAlgHom M f (single 
m a) = single m (f a)
参数：f : A ->ₐ[R] B；m : M；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.coeff_mapAlgHom`：coeff_mapAlgHom (f : A ->ₐ[R] B) (x : A[M
]) (m : M) : (mapAlgHom M f x).coeff m = f (x.coeff m)
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapAlgHom_single (f : A →ₐ[R] B) (m : M) (a : A) :
    mapAlgHom M f (single m a) = single m (f a) := by
  classical ext; simp [single_apply, apply_ite f]

@[to_additive (dont_translate := A) (attr := simp)]
/-
**MonoidAlgebra.mapAlgHom_id** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapAlgHom_id : mapAlgHom M (.id R A) = .id R A[M]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.algHom_ext`：algHom_ext ⦃φ₁ φ₂ : A[M] ->ₐ[R] B⦄ (single_one
_right : forall m, φ₁ (single m 1) = φ₂ (single m 1)) (single_one_left : φ₁.comp
 singleOneAlgH…
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.mapAlgHom_single`：mapAlgHom_single (f : A ->ₐ[R] B) (m : M
) (a : A) : mapAlgHom M f (single m a) = single m (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MonoidAlgebra.singleOneAlgHom_apply`：∀ {R : Type u_1} {A : Type u_4} {M 
: Type u_7} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]
   [inst_3 : Monoid M] (a…
-/
lemma mapAlgHom_id : mapAlgHom M (.id R A) = .id R A[M] := by ext <;> simp

@[to_additive (dont_translate := A B C) (attr := simp)]
/-
**MonoidAlgebra.mapRangeAlgHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapRangeAlgHom_comp (f : A ->ₐ[R] B) (g : B ->ₐ[R] C) : mapAlgHom M (g.com
p f) = (mapAlgHom M g).comp (mapAlgHom M f)
参数：f : A ->ₐ[R] B；g : B ->ₐ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.algHom_ext`：algHom_ext ⦃φ₁ φ₂ : A[M] ->ₐ[R] B⦄ (single_one
_right : forall m, φ₁ (single m 1) = φ₂ (single m 1)) (single_one_left : φ₁.comp
 singleOneAlgH…
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MonoidAlgebra.mapAlgHom_single`：mapAlgHom_single (f : A ->ₐ[R] B) (m : M
) (a : A) : mapAlgHom M f (single m a) = single m (f a)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `MonoidAlgebra.singleOneAlgHom_apply`：∀ {R : Type u_1} {A : Type u_4} {M 
: Type u_7} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]
   [inst_3 : Monoid M] (a…
-/
lemma mapRangeAlgHom_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    mapAlgHom M (g.comp f) = (mapAlgHom M g).comp (mapAlgHom M f) := by ext <;> simp

@[deprecated (since := "2026-06-18")] alias mapRangeAlgHom_single := mapAlgHom_single

variable (R M) in
/-- The algebra isomorphism of monoid algebras induced by an isomorphism of the base algebras. -/
@[to_additive (attr := simps apply)
/-- The algebra isomorphism of additive monoid algebras induced by an isomorphism of the base
algebras. -/]
/-
**MonoidAlgebra.mapAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapAlgEquiv (e : A ≃ₐ[R] B) : A[M] ≃ₐ[R] B[M] where __
参数：e : A ≃ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def mapAlgEquiv (e : A ≃ₐ[R] B) : A[M] ≃ₐ[R] B[M] where
  __ := mapAlgHom M e
  invFun := mapAlgHom M (e.symm : B →ₐ[R] A)
  left_inv _ := by aesop
  right_inv _ := by aesop

@[deprecated (since := "2026-06-18")] alias mapRangeAlgEquiv := mapAlgEquiv

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.symm_mapAlgEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：symm_mapAlgEquiv (e : A ≃ₐ[R] B) : (mapAlgEquiv R M e).symm = mapAlgEquiv 
R M e.symm
参数：e : A ≃ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_mapAlgEquiv (e : A ≃ₐ[R] B) : (mapAlgEquiv R M e).symm = mapAlgEquiv R M e.symm := rfl

@[deprecated (since := "2026-06-18")] alias symm_mapRangeAlgEquiv := symm_mapAlgEquiv

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapAlgEquiv_trans** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapAlgEquiv_trans (e₁ : A ≃ₐ[R] B) (e₂ : B ≃ₐ[R] C) : mapAlgEquiv R M (e₁.
trans e₂) = (mapAlgEquiv R M e₁).trans (mapAlgEquiv R M e₂)
参数：e₁ : A ≃ₐ[R] B；e₂ : B ≃ₐ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MonoidAlgebra.mapAlgEquiv_apply`：∀ (R : Type u_1) {A : Type u_4} {B : Ty
pe u_5} (M : Type u_7) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 :
 Semiring B] [inst_3 …
· 使用引理 `MonoidAlgebra.mapRingHom_comp`：mapRingHom_comp (f : S ->+* T) (g : R ->+
* S) : mapRingHom M (f.comp g) = (mapRingHom M f).comp (mapRingHom M g)
· 使用引理 `MonoidAlgebra.coeff_mapRingHom`：coeff_mapRingHom (f : R ->+* S) (x : R[M
]) (m : M) : (mapRingHom M f x).coeff m = f (x.coeff m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapAlgEquiv_trans (e₁ : A ≃ₐ[R] B) (e₂ : B ≃ₐ[R] C) :
    mapAlgEquiv R M (e₁.trans e₂) = (mapAlgEquiv R M e₁).trans (mapAlgEquiv R M e₂) := by ext; simp

@[deprecated (since := "2026-03-27")] alias mapRangeAlgEquiv_trans := mapAlgEquiv_trans

variable (R M) in
/-- `MonoidAlgebra.mapRangeAlgEquiv` as a `MonoidHom` from `A ≃ₐ[R] A`. -/
@[simps]
/-
**MonoidAlgebra.mapRangeAlgAut** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapRangeAlgAut : (A ≃ₐ[R] A) ->* A[M] ≃ₐ[R] A[M] where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MonoidAlgebra.mapRangeAlgEquiv` as a `MonoidHom` from `A ≃ₐ[R] A`.
-/
def mapRangeAlgAut : (A ≃ₐ[R] A) →* A[M] ≃ₐ[R] A[M] where
  toFun f := mapAlgEquiv _ _ f
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

end mapRange

section

variable (R) in
/-- When `V` is a `R[M]`-module, multiplication by a group element `g` is a `R`-linear map. -/
/-
**MonoidAlgebra.GroupSMul.linearMap** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra.Gro
upSMul`。
形式化陈述：(R : Type u_1) →   {M : Type u_7} →     [inst : Monoid M] →       [inst_1 
: CommSemiring R] →         (V : Type u_10) →           [inst_2 : AddCommMonoid 
V] →             [inst_3 : _root_.Module R V] →               [inst_4 : _root_.M
odule (MonoidAlgebra R M) V] → [IsScalarTower R (MonoidAlgebra R M) V] → M → V →
ₗ[R] V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `V` is a `R[M]`-module, multiplication by a group element `g` is a `R`-line
ar map.
-/
def GroupSMul.linearMap [Monoid M] [CommSemiring R] (V : Type*) [AddCommMonoid V] [Module R V]
    [Module R[M] V] [IsScalarTower R R[M] V] (g : M) : V →ₗ[R] V where
  toFun v := single g (1 : R) • v
  map_add' x y := smul_add (single g (1 : R)) x y
  map_smul' _c _x := smul_algebra_smul_comm _ _ _

variable (R) in
@[simp]
/-
**MonoidAlgebra.GroupSMul.linearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgeb
ra.GroupSMul`。
形式化陈述：∀ (R : Type u_1) {M : Type u_7} [inst : Monoid M] [inst_1 : CommSemiring R
] (V : Type u_10) [inst_2 : AddCommMonoid V]   [inst_3 : _root_.Module R V] [ins
t_4 : _root_.Module (MonoidAlgebra R M) V]   [inst_5 : IsScalarTower R (MonoidAl
gebra R M) V] (g : M) (v : V),   (MonoidAlgebra.GroupSMul.linearMap R V g) v = M
onoidAlgebra.single g 1 • v
参数：R : Type u_1；V : Type u_10；MonoidAlgebra R M；MonoidAlgebra R M；g : M；v : V；Mo
noidAlgebra.GroupSMul.linearMap R V g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem GroupSMul.linearMap_apply [Monoid M] [CommSemiring R] (V : Type*) [AddCommMonoid V]
    [Module R V] [Module R[M] V] [IsScalarTower R R[M] V] (g : M) (v : V) :
    (GroupSMul.linearMap R V g) v = single g (1 : R) • v :=
  rfl

variable [Monoid M] [CommSemiring R] {V W : Type*} [AddCommMonoid V] [Module R V]
  [Module R[M] V] [IsScalarTower R R[M] V] [AddCommMonoid W]
  [Module R W] [Module R[M] W] [IsScalarTower R R[M] W]
  (f : V →ₗ[R] W)

/-- Build a `R[M]`-linear map from a `R`-linear map and evidence that it is `M`-equivariant. -/
/-
**MonoidAlgebra.equivariantOfLinearOfComm** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgeb
ra`。
形式化陈述：equivariantOfLinearOfComm (h : forall (g : M) (v : V), f (single g (1 : R)
 • v) = single g (1 : R) • f v) : V ->ₗ[R[M]] W where toFun
参数：h : forall (g : M) (v : V), f (single g (1 : R) • v) = single g (1 : R) • f v
。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `R[M]`-linear map from a `R`-linear map and evidence that it is `M`-equi
variant.
-/
def equivariantOfLinearOfComm
    (h : ∀ (g : M) (v : V), f (single g (1 : R) • v) = single g (1 : R) • f v) :
    V →ₗ[R[M]] W where
  toFun := f
  map_add' v v' := by simp
  map_smul' c v := by
    refine induction c ?_ ?_
    · simp
    · intro g r c' _nm _nz w
      dsimp at *
      simp only [add_smul, f.map_add, w, single_eq_algebraMap_mul_of, ← smul_smul]
      rw [algebraMap_smul, algebraMap_smul, f.map_smul, of_apply, h g v]

variable (h : ∀ (g : M) (v : V), f (single g (1 : R) • v) = single g (1 : R) • f v)

@[simp]
/-
**MonoidAlgebra.equivariantOfLinearOfComm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Monoi
dAlgebra`。
形式化陈述：equivariantOfLinearOfComm_apply (v : V) : (equivariantOfLinearOfComm f h) 
v = f v
参数：v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivariantOfLinearOfComm_apply (v : V) : (equivariantOfLinearOfComm f h) v = f v :=
  rfl

end

variable [CommMonoid M] [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- If `S` is an `R`-algebra, then `S[M]` is a `R[M]` algebra.

Warning: This produces a diamond for `Algebra R[M] S[M][M]` and another one for `Algebra R[M] R[M]`.
That's why it is not a global instance. -/
@[to_additive
/-- If `S` is an `R`-algebra, then `S[M]` is an `R[M]`-algebra.

Warning: This produces a diamond for `Algebra R[M] S[M][M]` and another one for `Algebra R[M] R[M]`.
That's why it is not a global instance. -/]
/-
**MonoidAlgebra.algebraMonoidAlgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 `MonoidAlgebra`
。
形式化陈述：algebraMonoidAlgebra : Algebra R[M] S[M]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable abbrev algebraMonoidAlgebra : Algebra R[M] S[M] :=
  (mapRingHom M (algebraMap R S)).toAlgebra

scoped[AlgebraMonoidAlgebra] attribute [instance] MonoidAlgebra.algebraMonoidAlgebra
  AddMonoidAlgebra.algebraAddMonoidAlgebra

open scoped AlgebraMonoidAlgebra

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.algebraMap_def** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：algebraMap_def : algebraMap R[M] S[M] = mapRingHom M (algebraMap R S)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma algebraMap_def : algebraMap R[M] S[M] = mapRingHom M (algebraMap R S) := rfl

@[to_additive (dont_translate := R)]
/-
**MonoidAlgebra.isScalarTower_monoidAlgebra** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlg
ebra`。
形式化陈述：isScalarTower_monoidAlgebra [CommSemiring T] [Algebra R T] [Algebra S T] [
IsScalarTower R S T] : IsScalarTower R S[M] T[M]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
-/
lemma isScalarTower_monoidAlgebra [CommSemiring T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] : IsScalarTower R S[M] T[M] :=
  .of_algebraMap_eq' (mapAlgHom _ (IsScalarTower.toAlgHom R S T)).comp_algebraMap.symm

scoped[AlgebraMonoidAlgebra] attribute [instance] MonoidAlgebra.isScalarTower_monoidAlgebra
  AddMonoidAlgebra.vaddAssocClass_addMonoidAlgebra

end MonoidAlgebra

namespace AddMonoidAlgebra

/-! #### Non-unital, non-associative algebra structure -/

section NonUnitalNonAssocAlgebra

variable (R) [Semiring R] [Add M] [NonUnitalNonAssocSemiring A]

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
/-
**AddMonoidAlgebra.nonUnitalAlgHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlge
bra`。
形式化陈述：nonUnitalAlgHom_ext' [DistribMulAction R A] {φ₁ φ₂ : R[M] ->ₙₐ[R] A} (h : 
φ₁.toMulHom.comp (ofMagma R M) = φ₂.toMulHom.comp (ofMagma R M)) : φ₁ = φ₂
参数：h : φ₁.toMulHom.comp (ofMagma R M) = φ₂.toMulHom.comp (ofMagma R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.nonUnitalAlgHom_ext`：∀ (R : Type u_1) {A : Type u_4} {M
 : Type u_7} [inst : Semiring R] [inst_1 : Add M]   [inst_2 : NonUnitalNonAssocS
emiring A] [inst_3 : Distr…
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
See note [partially-applied ext lemmas].
-/
theorem nonUnitalAlgHom_ext' [DistribMulAction R A] {φ₁ φ₂ : R[M] →ₙₐ[R] A}
    (h : φ₁.toMulHom.comp (ofMagma R M) = φ₂.toMulHom.comp (ofMagma R M)) : φ₁ = φ₂ :=
  nonUnitalAlgHom_ext R <| DFunLike.congr_fun h

set_option backward.isDefEq.respectTransparency false in
/-- The functor `M ↦ R[M]`, from the category of magmas to the category of
non-unital, non-associative algebras over `R` is adjoint to the forgetful functor in the other
direction. -/
@[simps apply_apply symm_apply]
/-
**AddMonoidAlgebra.liftMagma** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：liftMagma [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] : (Mult
iplicative M ->ₙ* A) ≃ (R[M] ->ₙₐ[R] A) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `M ↦ R[M]`, from the category of magmas to the category of
non-unital, non-associative algebras over `R` is adjoint to the forgetful functo
r in the other
direction.
-/
def liftMagma [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    (Multiplicative M →ₙ* A) ≃ (R[M] →ₙₐ[R] A) where
  toFun f := {
    toAddMonoidHom :=
      (liftAddHom fun x ↦ (smulAddHom R A).flip (f <| .ofAdd x)).comp coeffAddEquiv.toAddMonoidHom
    map_smul' t' a := by simp [Finsupp.smul_sum, sum_smul_index', mul_smul]
    map_mul' a₁ a₂ := by
      simpa [mul_def, sum_sum_index, add_smul, Finsupp.mul_sum, Finsupp.sum_mul,
        smul_mul_smul_comm] using Finsupp.sum_comm ..
  }
  invFun F := F.toMulHom.comp (ofMagma R M)
  left_inv f := by ext; simp
  right_inv F := by ext; simp

end NonUnitalNonAssocAlgebra

/-! #### Algebra structure -/

section lift

variable [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- `liftNCRingHom` as an `AlgHom`, for when `f` is an `AlgHom` -/
/-
**AddMonoidAlgebra.liftNCAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：liftNCAlgHom (f : A ->ₐ[R] B) (g : Multiplicative M ->* B) (h_comm : foral
l x y, Commute (f x) (g y)) : A[M] ->ₐ[R] B
参数：f : A ->ₐ[R] B；g : Multiplicative M ->* B；h_comm : forall x y, Commute (f x) 
(g y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`liftNCRingHom` as an `AlgHom`, for when `f` is an `AlgHom`
-/
def liftNCAlgHom (f : A →ₐ[R] B) (g : Multiplicative M →* B) (h_comm : ∀ x y, Commute (f x) (g y)) :
    A[M] →ₐ[R] B :=
  { liftNCRingHom (f : A →+* B) g h_comm with
    commutes' := by simp [liftNCRingHom] }
/-
**AddMonoidAlgebra.coe_liftNCAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`
。
形式化陈述：∀ {R : Type u_1} {A : Type u_4} {B : Type u_5} {M : Type u_7} [inst : Comm
Semiring R] [inst_1 : AddMonoid M]   [inst_2 : Semiring A] [inst_3 : Algebra R A
] [inst_4 : Semiring B] [inst_5 : Algebra R B] (f : A →ₐ[R] B)   (g : Multiplica
tive M →* B) (h_comm : ∀ (x : A) (y : Multiplicative M), Commute (f x) (g y)),  
 ⇑(AddMonoidAlgebra.liftNCAlgHom f g h_comm) = ⇑(AddMonoidAlgebra.liftNC ↑f ⇑g)
参数：f : A →ₐ[R] B；g : Multiplicative M →* B；h_comm : ∀ (x : A) (y : Multiplicativ
e M), Commute (f x) (g y)；AddMonoidAlgebra.liftNCAlgHom f g h_comm；AddMonoidAlge
bra.liftNC ↑f ⇑g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_liftNCAlgHom (f : A →ₐ[R] B) (g : Multiplicative M →* B) (h_comm) :
    ⇑(liftNCAlgHom f g h_comm) = liftNC f g := rfl

/-- Version of `algHom_ext` where both assumptions are written as equalities of bundled homs. -/
/-
**AddMonoidAlgebra.algHom_ext'** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：algHom_ext' ⦃φ₁ φ₂ : A[M] ->ₐ[R] B⦄ (single_one_right : (φ₁ : A[M] ->* B).
comp (of A M) = (φ₂ : A[M] ->* B).comp (of A M)) (single_one_left : φ₁.comp sing
leZeroAlgHom = φ₂.comp singleZeroAlgHom) : φ₁ = φ₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AddMonoidAlgebra.algHom_ext`：∀ {R : Type u_1} {A : Type u_4} {B : Type u
_5} {M : Type u_7} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Version of `algHom_ext` where both assumptions are written as equalities of bund
led homs.
-/
lemma algHom_ext' ⦃φ₁ φ₂ : A[M] →ₐ[R] B⦄
    (single_one_right : (φ₁ : A[M] →* B).comp (of A M) = (φ₂ : A[M] →* B).comp (of A M))
    (single_one_left : φ₁.comp singleZeroAlgHom = φ₂.comp singleZeroAlgHom) : φ₁ = φ₂ :=
  algHom_ext (congr($single_one_right ·)) single_one_left

set_option backward.isDefEq.respectTransparency false in
variable (R M A) in
/-- Any monoid homomorphism `M →* A` can be lifted to an algebra homomorphism
`R[M] →ₐ[R] A`. -/
/-
**AddMonoidAlgebra.lift** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：lift : (Multiplicative M ->* A) ≃ (R[M] ->ₐ[R] A) where toFun F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any monoid homomorphism `M →* A` can be lifted to an algebra homomorphism
`R[M] →ₐ[R] A`.
-/
def lift : (Multiplicative M →* A) ≃ (R[M] →ₐ[R] A) where
  toFun F := liftNCAlgHom (Algebra.ofId R A) F fun _ _ => Algebra.commutes _ _
  invFun f := (f : R[M] →* A).comp (of R M)
  left_inv f := by ext; simp
  right_inv F := by ext; simp
/-
**AddMonoidAlgebra.lift_apply'** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：lift_apply' (F : Multiplicative M ->* A) (f : R[M]) : lift R A M F f = f.c
oeff.sum fun a b => algebraMap R A b * F (.ofAdd a)
参数：F : Multiplicative M ->* A；f : R[M]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_apply' (F : Multiplicative M →* A) (f : R[M]) :
    lift R A M F f = f.coeff.sum fun a b => algebraMap R A b * F (.ofAdd a) := rfl
/-
**AddMonoidAlgebra.lift_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：lift_apply (F : Multiplicative M ->* A) (f : R[M]) : lift R A M F f = f.co
eff.sum fun a b => b • F (.ofAdd a)
参数：F : Multiplicative M ->* A；f : R[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_apply (F : Multiplicative M →* A) (f : R[M]) :
    lift R A M F f = f.coeff.sum fun a b => b • F (.ofAdd a) := by
  simp only [lift_apply', Algebra.smul_def]
/-
**AddMonoidAlgebra.lift_def** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：lift_def (F : Multiplicative M ->* A) : ⇑(lift R A M F) = liftNC ((algebra
Map R A : R ->+* A) : R ->+ A) F
参数：F : Multiplicative M ->* A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_def (F : Multiplicative M →* A) :
    ⇑(lift R A M F) = liftNC ((algebraMap R A : R →+* A) : R →+ A) F :=
  rfl

@[simp]
/-
**AddMonoidAlgebra.lift_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：lift_symm_apply (F : R[M] ->ₐ[R] A) (x : Multiplicative M) : (lift R A M).
symm F x = F (single x.toAdd 1)
参数：F : R[M] ->ₐ[R] A；x : Multiplicative M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem lift_symm_apply (F : R[M] →ₐ[R] A) (x : Multiplicative M) :
    (lift R A M).symm F x = F (single x.toAdd 1) :=
  rfl
/-
**AddMonoidAlgebra.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：lift_of (F : Multiplicative M ->* A) (x : Multiplicative M) : lift R A M F
 (of R M x) = F x
参数：F : Multiplicative M ->* A；x : Multiplicative M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.lift_of`：lift_of (F : M ->* A) (m : M) : lift R A M F (of 
R M m) = F m
-/
theorem lift_of (F : Multiplicative M →* A) (x : Multiplicative M) :
    lift R A M F (of R M x) = F x := MonoidAlgebra.lift_of F x

@[simp]
/-
**AddMonoidAlgebra.lift_single** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：lift_single (F : Multiplicative M ->* A) (a b) : lift R A M F (single a b)
 = b • F (Multiplicative.ofAdd a)
参数：F : Multiplicative M ->* A；a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.lift_single`：lift_single (F : M ->* A) (a b) : lift R A M 
F (single a b) = b • F a
-/
theorem lift_single (F : Multiplicative M →* A) (a b) :
    lift R A M F (single a b) = b • F (Multiplicative.ofAdd a) :=
  MonoidAlgebra.lift_single F (.ofAdd a) b
/-
**AddMonoidAlgebra.lift_of'** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：lift_of' (F : Multiplicative M ->* A) (x : M) : lift R A M F (of' R M x) =
 F (Multiplicative.ofAdd x)
参数：F : Multiplicative M ->* A；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.lift_of`：lift_of (F : Multiplicative M ->* A) (x : Mult
iplicative M) : lift R A M F (of R M x) = F x
-/
lemma lift_of' (F : Multiplicative M →* A) (x : M) :
    lift R A M F (of' R M x) = F (Multiplicative.ofAdd x) :=
  lift_of F x
/-
**AddMonoidAlgebra.lift_unique'** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：lift_unique' (F : R[M] ->ₐ[R] A) : F = lift R A M ((F : R[M] ->* A).comp (
of R M))
参数：F : R[M] ->ₐ[R] A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem lift_unique' (F : R[M] →ₐ[R] A) :
    F = lift R A M ((F : R[M] →* A).comp (of R M)) :=
  ((lift R A M).apply_symm_apply F).symm

/-- Decomposition of a `R`-algebra homomorphism from `R[M]` by
its values on `F (single a 1)`. -/
/-
**AddMonoidAlgebra.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：lift_unique (F : R[M] ->ₐ[R] A) (f : R[M]) : F f = f.coeff.sum fun m r => 
r • F (single m 1)
参数：F : R[M] ->ₐ[R] A；f : R[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.lift_unique'`：lift_unique' (F : R[M] ->ₐ[R] A) : F = li
ft R A M ((F : R[M] ->* A).comp (of R M))
· 使用定理 `AddMonoidAlgebra.lift_apply`：lift_apply (F : Multiplicative M ->* A) (f 
: R[M]) : lift R A M F f = f.coeff.sum fun a b => b • F (.ofAdd a)

--- 原说明 ---
Decomposition of a `R`-algebra homomorphism from `R[M]` by
its values on `F (single a 1)`.
-/
theorem lift_unique (F : R[M] →ₐ[R] A) (f : R[M]) :
    F f = f.coeff.sum fun m r => r • F (single m 1) := by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]
/-
**AddMonoidAlgebra.lift_mapRingHom_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `AddMono
idAlgebra`。
形式化陈述：lift_mapRingHom_algebraMap [CommSemiring S] [Algebra S A] [Algebra R S] [I
sScalarTower R S A] (f : Multiplicative M ->* A) (x : R[M]) : lift _ _ _ f (mapR
ingHom _ (algebraMap R S) x) = lift _ _ _ f x
参数：f : Multiplicative M ->* A；x : R[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.induction`：∀ {R : Type u_1} {M : Type u_4} [inst : Semi
ring R] {motive : AddMonoidAlgebra R M → Prop} (x : AddMonoidAlgebra R M),   mot
ive 0 →     (∀ (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddMonoidAlgebra.mapRingHom_single`：∀ {R : Type u_3} {S : Type u_4} {M :
 Type u_6} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : AddMonoid M]   (f
 : R →+* S) (a : M) (b :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AddMonoidAlgebra.lift_single`：lift_single (F : Multiplicative M ->* A) (
a b) : lift R A M F (single a b) = b • F (Multiplicative.ofAdd a)
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
-/
lemma lift_mapRingHom_algebraMap [CommSemiring S] [Algebra S A] [Algebra R S] [IsScalarTower R S A]
    (f : Multiplicative M →* A) (x : R[M]) :
    lift _ _ _ f (mapRingHom _ (algebraMap R S) x) = lift _ _ _ f x := by
  induction x using induction with
  | zero => simp
  | single_add a b f _ _ ih => simp [ih]

@[deprecated (since := "2026-06-18")]
alias lift_mapRangeRingHom_algebraMap := lift_mapRingHom_algebraMap

variable (R A) in
/-- `AddMonoidAlgebra.domCongr` as an `AddMonoidHom` from `AddAut`. -/
@[simps]
/-
**AddMonoidAlgebra.domCongrAut** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：domCongrAut : AddAut M ->+ Additive (A[M] ≃ₐ[R] A[M]) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddMonoidAlgebra.domCongr` as an `AddMonoidHom` from `AddAut`.
-/
def domCongrAut : AddAut M →+ Additive (A[M] ≃ₐ[R] A[M]) where
  toFun f := .ofMul (AddMonoidAlgebra.domCongr R A f)
  map_zero' := by ext; simp [AddAut.zero_def]
  map_add' _ _ := by ext; simp [AddAut.add_def]

end lift

variable [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A]

variable (R M) in
/-- `AddMonoidAlgebra.mapAlgEquiv` as an `AddMonoidHom` from `R ≃ₐ[k] R`. -/
@[simps]
/-
**AddMonoidAlgebra.mapAlgAut** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：mapAlgAut : (A ≃ₐ[R] A) ->* A[M] ≃ₐ[R] A[M] where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddMonoidAlgebra.mapAlgEquiv` as an `AddMonoidHom` from `R ≃ₐ[k] R`.
-/
def mapAlgAut : (A ≃ₐ[R] A) →* A[M] ≃ₐ[R] A[M] where
  toFun f := mapAlgEquiv _ _ f
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

end AddMonoidAlgebra

variable [CommSemiring R] [Semiring A] [Algebra R A]

namespace AddMonoidAlgebra
variable [AddMonoid M]

variable (R A M) in
/-- The algebra equivalence between `AddMonoidAlgebra` and `MonoidAlgebra` in terms of
`Multiplicative`. -/
@[simps!]
/-
**AddMonoidAlgebra.toMultiplicativeAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoid
Algebra`。
形式化陈述：toMultiplicativeAlgEquiv : AddMonoidAlgebra A M ≃ₐ[R] MonoidAlgebra A (Mul
tiplicative M) where toRingEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra equivalence between `AddMonoidAlgebra` and `MonoidAlgebra` in terms 
of
`Multiplicative`.
-/
def toMultiplicativeAlgEquiv : AddMonoidAlgebra A M ≃ₐ[R] MonoidAlgebra A (Multiplicative M) where
  toRingEquiv := toMultiplicative A M
  commutes' r := by ext; simp

@[simp]
/-
**AddMonoidAlgebra.toMultiplicativeAlgEquiv_single** 是 Mathlib 中的一个引理，位于命名空间 `Ad
dMonoidAlgebra`。
形式化陈述：toMultiplicativeAlgEquiv_single (m : M) (a : A) : toMultiplicativeAlgEquiv
 R A M (single m a) = .single (.ofAdd m) a
参数：m : M；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.coeff_toMultiplicativeAlgEquiv_apply`：∀ (R : Type u_1) 
(A : Type u_4) (M : Type u_7) [inst : CommSemiring R] [inst_1 : Semiring A] [ins
t_2 : Algebra R A]   [inst_3 : AddMonoid M]…
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toMultiplicativeAlgEquiv_single (m : M) (a : A) :
    toMultiplicativeAlgEquiv R A M (single m a) = .single (.ofAdd m) a := by ext; simp

end AddMonoidAlgebra

namespace MonoidAlgebra
variable [Monoid M]

variable (R A M) in
/-- The algebra equivalence between `MonoidAlgebra` and `AddMonoidAlgebra` in terms of
`Additive`. -/
@[simps!]
/-
**MonoidAlgebra.toAdditiveAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：toAdditiveAlgEquiv : MonoidAlgebra A M ≃ₐ[R] AddMonoidAlgebra A (Additive 
M) where toRingEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra equivalence between `MonoidAlgebra` and `AddMonoidAlgebra` in terms 
of
`Additive`.
-/
def toAdditiveAlgEquiv : MonoidAlgebra A M ≃ₐ[R] AddMonoidAlgebra A (Additive M) where
  toRingEquiv := toAdditive A M
  commutes' r := by simp [toAdditive]

@[simp]
/-
**MonoidAlgebra.toAdditiveAlgEquiv_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgeb
ra`。
形式化陈述：toAdditiveAlgEquiv_single (m : M) (a : A) : toAdditiveAlgEquiv R A M (sing
le m a) = .single (.ofMul m) a
参数：m : M；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.coeff_toAdditiveAlgEquiv_apply`：∀ (R : Type u_1) (A : Type
 u_4) (M : Type u_7) [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Alg
ebra R A]   [inst_3 : Monoid M] (x…
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toAdditiveAlgEquiv_single (m : M) (a : A) :
    toAdditiveAlgEquiv R A M (single m a) = .single (.ofMul m) a := by ext; simp

end MonoidAlgebra

