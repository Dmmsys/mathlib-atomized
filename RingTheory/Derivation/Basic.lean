/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Derivations

This file defines derivation. A derivation `D` from the `R`-algebra `A` to the `A`-module `M` is an
`R`-linear map that satisfy the Leibniz rule `D (a * b) = a * D b + D a * b`.

## Main results

- `Derivation`: The type of `R`-derivations from `A` to `M`. This has an `A`-module structure.
- `Derivation.llcomp`: We may compose linear maps and derivations to obtain a derivation,
  and the composition is bilinear.

See `Mathlib/RingTheory/Derivation/Lie.lean` for
- `Derivation.instLieAlgebra`: The `R`-derivations from `A` to `A` form a Lie algebra over `R`.

and `Mathlib/RingTheory/Derivation/ToSquareZero.lean` for
- `derivationToSquareZeroEquivLift`: The `R`-derivations from `A` into a square-zero ideal `I`
  of `B` corresponds to the lifts `A →ₐ[R] B` of the map `A →ₐ[R] B ⧸ I`.

## Future project

- Generalize derivations into bimodules.

-/

@[expose] public section

open Algebra

/-- `D : Derivation R A M` is an `R`-linear map from `A` to `M` that satisfies the `leibniz`
equality. We also require that `D 1 = 0`. See `Derivation.mk'` for a constructor that deduces this
assumption from the Leibniz rule when `M` is cancellative.

TODO: update this when bimodules are defined. -/
/-
**Derivation** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (A : Type u_2) →     (M : Type u_3) →       [inst : Com
mSemiring R] →         [inst_1 : CommSemiring A] →           [inst_2 : AddCommMo
noid M] → [Algebra R A] → [_root_.Module A M] → [_root_.Module R M] → Type (max 
u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`D : Derivation R A M` is an `R`-linear map from `A` to `M` that satisfies the `
leibniz`
equality. We also require that `D 1 = 0`. See `Derivation.mk'` for a constructor
 that deduces this
assumption from the Leibniz rule when `M` is cancellative.

TODO: update this when bimodules are defined.
-/
structure Derivation (R : Type*) (A : Type*) (M : Type*)
    [CommSemiring R] [CommSemiring A] [AddCommMonoid M] [Algebra R A] [Module A M] [Module R M]
    extends A →ₗ[R] M where
  protected map_one_eq_zero' : toLinearMap 1 = 0
  protected leibniz' (a b : A) : toLinearMap (a * b) = a • toLinearMap b + b • toLinearMap a

/-- The `LinearMap` underlying a `Derivation`. -/
add_decl_doc Derivation.toLinearMap

namespace Derivation

section

variable {R : Type*} {A : Type*} {B : Type*} {M : Type*}
variable [CommSemiring R] [CommSemiring A] [CommSemiring B] [AddCommMonoid M]
variable [Algebra R A] [Algebra R B]
variable [Module A M] [Module B M] [Module R M]


variable (D : Derivation R A M) {D1 D2 : Derivation R A M} (r : R) (a b : A)

/-
**Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (Derivation R A M) A M where
  coe D := D.toFun
  coe_injective D1 D2 h := by cases D1; cases D2; congr; exact DFunLike.coe_injective h
/-
**Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddMonoidHomClass (Derivation R A M) A M where
  map_add D := D.toLinearMap.map_add'
  map_zero D := D.toLinearMap.map_zero

-- Not a simp lemma because it can be proved via `coeFn_coe` + `toLinearMap_eq_coe`
/-
**Derivation.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：toFun_eq_coe : D.toFun = ⇑D
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe : D.toFun = ⇑D :=
  rfl

/-- See Note [custom simps projection] -/
/-
**Derivation.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `Derivation.Simps`。
形式化陈述：{R : Type u_1} →   {A : Type u_2} →     {M : Type u_4} →       [inst : Com
mSemiring R] →         [inst_1 : CommSemiring A] →           [inst_2 : AddCommMo
noid M] →             [inst_3 : Algebra R A] →               [inst_4 : _root_.Mo
dule A M] → [inst_5 : _root_.Module R M] → Derivation R A M → A → M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.apply (D : Derivation R A M) : A → M := D

initialize_simps_projections Derivation (toFun → apply)

attribute [coe] toLinearMap
/-
**Derivation.hasCoeToLinearMap** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
形式化陈述：hasCoeToLinearMap : Coe (Derivation R A M) (A ->ₗ[R] M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeToLinearMap : Coe (Derivation R A M) (A →ₗ[R] M) :=
  ⟨fun D => D.toLinearMap⟩

@[simp]
/-
**Derivation.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：mk_coe (f : A ->ₗ[R] M) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : Derivation R A M) : A ->
 M) = f
参数：f : A ->ₗ[R] M；h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_coe (f : A →ₗ[R] M) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : Derivation R A M) : A → M) = f :=
  rfl

@[simp, norm_cast]
/-
**Derivation.coeFn_coe** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：coeFn_coe (f : Derivation R A M) : ⇑(f : A ->ₗ[R] M) = f
参数：f : Derivation R A M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_coe (f : Derivation R A M) : ⇑(f : A →ₗ[R] M) = f :=
  rfl
/-
**Derivation.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：coe_injective : @Function.Injective (Derivation R A M) (A -> M) DFunLike.c
oe
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_injective : @Function.Injective (Derivation R A M) (A → M) DFunLike.coe :=
  DFunLike.coe_injective

@[ext]
/-
**Derivation.ext** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：ext (H : forall a, D1 a = D2 a) : D1 = D2
参数：H : forall a, D1 a = D2 a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext (H : ∀ a, D1 a = D2 a) : D1 = D2 :=
  DFunLike.ext _ _ H
/-
**Derivation.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：congr_fun (h : D1 = D2) (a : A) : D1 a = D2 a
参数：h : D1 = D2；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem congr_fun (h : D1 = D2) (a : A) : D1 a = D2 a :=
  DFunLike.congr_fun h a
/-
**Derivation.map_add** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {M : Type u_4} [inst : CommSemiring R] [in
st_1 : CommSemiring A]   [inst_2 : AddCommMonoid M] [inst_3 : Algebra R A] [inst
_4 : _root_.Module A M] [inst_5 : _root_.Module R M]   (D : Derivation R A M) (a
 b : A), D (a + b) = D a + D b
参数：D : Derivation R A M；a b : A；a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
-/
protected theorem map_add : D (a + b) = D a + D b :=
  map_add D a b
/-
**Derivation.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {M : Type u_4} [inst : CommSemiring R] [in
st_1 : CommSemiring A]   [inst_2 : AddCommMonoid M] [inst_3 : Algebra R A] [inst
_4 : _root_.Module A M] [inst_5 : _root_.Module R M]   (D : Derivation R A M), D
 0 = 0
参数：D : Derivation R A M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
-/
protected theorem map_zero : D 0 = 0 :=
  map_zero D

@[simp]
/-
**Derivation.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：map_smul : D (r • a) = r • D a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
theorem map_smul : D (r • a) = r • D a :=
  D.toLinearMap.map_smul r a

@[simp]
/-
**Derivation.leibniz** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：leibniz : D (a * b) = a • D b + b • D a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.leibniz'`：∀ {R : Type u_1} {A : Type u_2} {M : Type u_3} [ins
t : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMonoid M] [inst
_3 : Alge…
-/
theorem leibniz : D (a * b) = a • D b + b • D a :=
  D.leibniz' _ _

@[simp]
/-
**Derivation.map_smul_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：map_smul_of_tower {S : Type*} [SMul S A] [SMul S M] [LinearMap.CompatibleS
Mul A M S R] (D : Derivation R A M) (r : S) (a : A) : D (r • a) = r • D a
参数：D : Derivation R A M；r : S；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
-/
theorem map_smul_of_tower {S : Type*} [SMul S A] [SMul S M] [LinearMap.CompatibleSMul A M S R]
    (D : Derivation R A M) (r : S) (a : A) : D (r • a) = r • D a :=
  D.toLinearMap.map_smul_of_tower r a

@[simp]
/-
**Derivation.map_one_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：map_one_eq_zero : D 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.map_one_eq_zero'`：∀ {R : Type u_1} {A : Type u_2} {M : Type u
_3} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMonoid 
M] [inst_3 : Alge…
-/
theorem map_one_eq_zero : D 1 = 0 :=
  D.map_one_eq_zero'

@[simp]
/-
**Derivation.map_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：map_algebraMap : D (algebraMap R A r) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
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
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Derivation.map_smul`：map_smul : D (r • a) = r • D a
· 使用定理 `Derivation.map_one_eq_zero`：map_one_eq_zero : D 1 = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem map_algebraMap : D (algebraMap R A r) = 0 := by
  rw [← mul_one r, map_mul, map_one, ← smul_def, map_smul, map_one_eq_zero, smul_zero]

@[simp]
/-
**Derivation.map_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：map_natCast (n : Nat) : D (n : A) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用定理 `Derivation.map_smul_of_tower`：map_smul_of_tower {S : Type*} [SMul S A] [
SMul S M] [LinearMap.CompatibleSMul A M S R] (D : Derivation R A M) (r : S) (a :
 A) : D (r • a) = …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Derivation.map_one_eq_zero`：map_one_eq_zero : D 1 = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem map_natCast (n : ℕ) : D (n : A) = 0 := by
  rw [← nsmul_one, D.map_smul_of_tower n, map_one_eq_zero, smul_zero]

@[simp]
/-
**Derivation.leibniz_pow** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：leibniz_pow (n : Nat) : D (a ^ n) = n • a ^ (n - 1) • D a
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Derivation.map_one_eq_zero`：map_one_eq_zero : D 1 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Derivation.leibniz`：leibniz : D (a * b) = a • D b + b • D a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `one_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 1 • a = a
-/
theorem leibniz_pow (n : ℕ) : D (a ^ n) = n • a ^ (n - 1) • D a := by
  induction n with
  | zero => rw [pow_zero, map_one_eq_zero, zero_smul]
  | succ n ihn =>
    rcases eq_zero_or_pos n with (rfl | hpos)
    · simp
    · have : a * a ^ (n - 1) = a ^ n := by rw [← pow_succ', Nat.sub_add_cancel hpos]
      simp only [pow_succ', leibniz, ihn, smul_comm a n (_ : M), smul_smul a, add_smul, this,
        Nat.add_succ_sub_one, add_zero, one_nsmul]

open Polynomial in
@[simp]
/-
**Derivation.map_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：map_aeval (P : R[X]) (x : A) : D (aeval x P) = aeval x (derivative P) • D 
x
参数：P : R[X]；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on`：∀ {R : Type u} [inst : Semiring R] {motive : Po
lynomial R → Prop} (p : Polynomial R),   (∀ (a : R), motive (Polynomial.C a)) → 
    (∀ (p q :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Derivation.map_algebraMap`：map_algebraMap : D (algebraMap R A r) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.derivative_C`：derivative_C {a : R} : derivative (C a) = 0
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
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
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
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `Polynomial.derivative_add`：derivative_add {f g : R[X]} : derivative (f +
 g) = derivative f + derivative g
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Derivation.leibniz`：leibniz : D (a * b) = a • D b + b • D a
· 使用定理 `Derivation.leibniz_pow`：leibniz_pow (n : Nat) : D (a ^ n) = n • a ^ (n -
 1) • D a
（共 49 条，此处仅展示前 30 条）
-/
theorem map_aeval (P : R[X]) (x : A) :
    D (aeval x P) = aeval x (derivative P) • D x := by
  induction P using Polynomial.induction_on
  · simp
  · simp [add_smul, *]
  · simp [mul_smul, ← Nat.cast_smul_eq_nsmul A]
/-
**Derivation.eqOn_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：eqOn_adjoin {s : Set A} (h : Set.EqOn D1 D2 s) : Set.EqOn D1 D2 (adjoin R 
s)
参数：h : Set.EqOn D1 D2 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_induction`：adjoin_induction {p : (x : A) -> x in adjoin R
 s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_adjoin hx)) (algebraMap
 : forall r, p…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Derivation.map_algebraMap`：map_algebraMap : D (algebraMap R A r) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Derivation.leibniz`：leibniz : D (a * b) = a • D b + b • D a
-/
theorem eqOn_adjoin {s : Set A} (h : Set.EqOn D1 D2 s) : Set.EqOn D1 D2 (adjoin R s) := fun _ hx =>
  Algebra.adjoin_induction (hx := hx) h
    (fun r => (D1.map_algebraMap r).trans (D2.map_algebraMap r).symm)
    (fun x y _ _ hx hy => by simp only [map_add, *]) fun x y _ _ hx hy => by simp only [leibniz, *]

/-- If adjoin of a set is the whole algebra, then any two derivations equal on this set are equal
on the whole algebra. -/
/-
**Derivation.ext_of_adjoin_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：ext_of_adjoin_eq_top (s : Set A) (hs : adjoin R s = ⊤) (h : Set.EqOn D1 D2
 s) : D1 = D2
参数：s : Set A；hs : adjoin R s = ⊤；h : Set.EqOn D1 D2 s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.ext`：ext (H : forall a, D1 a = D2 a) : D1 = D2
· 使用定理 `Derivation.eqOn_adjoin`：eqOn_adjoin {s : Set A} (h : Set.EqOn D1 D2 s) :
 Set.EqOn D1 D2 (adjoin R s)
· 使用定理 `trivial`：True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If adjoin of a set is the whole algebra, then any two derivations equal on this 
set are equal
on the whole algebra.
-/
theorem ext_of_adjoin_eq_top (s : Set A) (hs : adjoin R s = ⊤) (h : Set.EqOn D1 D2 s) : D1 = D2 :=
  ext fun _ => eqOn_adjoin h <| hs.symm ▸ trivial

-- Data typeclasses
/-
**Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (Derivation R A M) :=
  ⟨{  toLinearMap := 0
      map_one_eq_zero' := rfl
      leibniz' := fun a b => by simp only [add_zero, LinearMap.zero_apply, smul_zero] }⟩

@[simp]
/-
**Derivation.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：coe_zero : ⇑(0 : Derivation R A M) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ⇑(0 : Derivation R A M) = 0 :=
  rfl

@[simp]
/-
**Derivation.coe_zero_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：coe_zero_linearMap : ↑(0 : Derivation R A M) = (0 : A ->ₗ[R] M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero_linearMap : ↑(0 : Derivation R A M) = (0 : A →ₗ[R] M) :=
  rfl
/-
**Derivation.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：zero_apply (a : A) : (0 : Derivation R A M) a = 0
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (a : A) : (0 : Derivation R A M) a = 0 :=
  rfl
/-
**Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (Derivation R A M) :=
  ⟨fun D1 D2 =>
    { toLinearMap := D1 + D2
      map_one_eq_zero' := by simp
      leibniz' := fun a b => by
        simp only [leibniz, LinearMap.add_apply, coeFn_coe, smul_add, add_add_add_comm] }⟩

@[simp]
/-
**Derivation.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：coe_add (D1 D2 : Derivation R A M) : ⇑(D1 + D2) = D1 + D2
参数：D1 D2 : Derivation R A M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (D1 D2 : Derivation R A M) : ⇑(D1 + D2) = D1 + D2 :=
  rfl

@[simp]
/-
**Derivation.coe_add_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：coe_add_linearMap (D1 D2 : Derivation R A M) : ↑(D1 + D2) = (D1 + D2 : A -
>ₗ[R] M)
参数：D1 D2 : Derivation R A M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add_linearMap (D1 D2 : Derivation R A M) : ↑(D1 + D2) = (D1 + D2 : A →ₗ[R] M) :=
  rfl
/-
**Derivation.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：add_apply : (D1 + D2) a = D1 a + D2 a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply : (D1 + D2) a = D1 a + D2 a :=
  rfl
/-
**Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Derivation R A M) :=
  ⟨0⟩

section Scalar

variable {S T : Type*}
variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M] [SMulCommClass S A M]
variable [Monoid T] [DistribMulAction T M] [SMulCommClass R T M] [SMulCommClass T A M]

/-
**Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul S (Derivation R A M) :=
  ⟨fun r D =>
    { toLinearMap := r • D.1
      map_one_eq_zero' := by rw [LinearMap.smul_apply, coeFn_coe, D.map_one_eq_zero, smul_zero]
      leibniz' := fun a b => by simp only [LinearMap.smul_apply, coeFn_coe, leibniz, smul_add,
        smul_comm r (_ : A) (_ : M)] }⟩

@[simp]
/-
**Derivation.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：coe_smul (r : S) (D : Derivation R A M) : ⇑(r • D) = r • ⇑D
参数：r : S；D : Derivation R A M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul (r : S) (D : Derivation R A M) : ⇑(r • D) = r • ⇑D :=
  rfl

@[simp]
/-
**Derivation.coe_smul_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：coe_smul_linearMap (r : S) (D : Derivation R A M) : ↑(r • D) = r • (D : A 
->ₗ[R] M)
参数：r : S；D : Derivation R A M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul_linearMap (r : S) (D : Derivation R A M) : ↑(r • D) = r • (D : A →ₗ[R] M) :=
  rfl
/-
**Derivation.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：smul_apply (r : S) (D : Derivation R A M) : (r • D) a = r • D a
参数：r : S；D : Derivation R A M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply (r : S) (D : Derivation R A M) : (r • D) a = r • D a :=
  rfl
/-
**Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid (Derivation R A M) :=
  coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

/-- `coeFn` as an `AddMonoidHom`. -/
/-
**Derivation.coeFnAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Derivation`。
形式化陈述：coeFnAddMonoidHom : Derivation R A M ->+ A -> M where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.coe_zero`：coe_zero : ⇑(0 : Derivation R A M) = 0
· 使用定理 `Derivation.coe_add`：coe_add (D1 D2 : Derivation R A M) : ⇑(D1 + D2) = D1
 + D2

--- 原说明 ---
`coeFn` as an `AddMonoidHom`.
-/
def coeFnAddMonoidHom : Derivation R A M →+ A → M where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
/-
**Derivation.coeFnAddMonoidHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Derivation`。
形式化陈述：coeFnAddMonoidHom_apply (D : Derivation R A M) : coeFnAddMonoidHom D = D
参数：D : Derivation R A M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeFnAddMonoidHom_apply (D : Derivation R A M) : coeFnAddMonoidHom D = D := rfl
/-
**Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribMulAction S (Derivation R A M) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul
/-
**Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DistribMulAction Sᵐᵒᵖ M] [IsCentralScalar S M] :
    IsCentralScalar S (Derivation R A M) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _
/-
**Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul S T] [IsScalarTower S T M] : IsScalarTower S T (Derivation R A M) :=
  ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩
/-
**Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass S T M] : SMulCommClass S T (Derivation R A M) :=
  ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

end Scalar

/-
**Derivation.instModule** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
形式化陈述：instModule {S : Type*} [Semiring S] [Module S M] [SMulCommClass R S M] [SM
ulCommClass S A M] : Module S (Derivation R A M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.coe_injective`：coe_injective : @Function.Injective (Derivatio
n R A M) (A -> M) DFunLike.coe
-/
instance instModule {S : Type*} [Semiring S] [Module S M] [SMulCommClass R S M]
    [SMulCommClass S A M] : Module S (Derivation R A M) :=
  Function.Injective.module S coeFnAddMonoidHom coe_injective coe_smul

section PushForward

variable {N : Type*} [AddCommMonoid N] [Module A N] [Module R N] [IsScalarTower R A M]
  [IsScalarTower R A N]

variable (f : M →ₗ[A] N) (e : M ≃ₗ[A] N)

set_option backward.isDefEq.respectTransparency false in
/-- We can push forward derivations using linear maps, i.e., the composition of a derivation with a
linear map is a derivation. Furthermore, this operation is linear on the spaces of derivations. -/
/-
**Derivation._root_.LinearMap.compDer** 是 Mathlib 中的一个定义，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can push forward derivations using linear maps, i.e., the composition of a de
rivation with a
linear map is a derivation. Furthermore, this operation is linear on the spaces 
of derivations.
-/
def _root_.LinearMap.compDer : Derivation R A M →ₗ[A] Derivation R A N where
  toFun D :=
    { toLinearMap := (f : M →ₗ[R] N).comp (D : A →ₗ[R] M)
      map_one_eq_zero' := by simp only [LinearMap.comp_apply, coeFn_coe, map_one_eq_zero, map_zero]
      leibniz' := fun a b => by
        simp only [coeFn_coe, LinearMap.comp_apply, map_add, leibniz,
          LinearMap.coe_restrictScalars, LinearMap.map_smul] }
  map_add' D₁ D₂ := by ext; exact LinearMap.map_add _ _ _
  map_smul' r D := by ext; dsimp; simp only [_root_.map_smul]

@[simp]
/-
**Derivation.coe_to_linearMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：coe_to_linearMap_comp : (f.compDer D : A ->ₗ[R] N) = (f : M ->ₗ[R] N).comp
 (D : A ->ₗ[R] M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem coe_to_linearMap_comp : (f.compDer D : A →ₗ[R] N) = (f : M →ₗ[R] N).comp (D : A →ₗ[R] M) :=
  rfl

@[simp]
/-
**Derivation.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：coe_comp : (f.compDer D : A -> N) = (f : M ->ₗ[R] N).comp (D : A ->ₗ[R] M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem coe_comp : (f.compDer D : A → N) = (f : M →ₗ[R] N).comp (D : A →ₗ[R] M) :=
  rfl

/-- The composition of a derivation with a linear map as a bilinear map -/
@[simps]
/-
**Derivation.llcomp** 是 Mathlib 中的一个定义，位于命名空间 `Derivation`。
形式化陈述：llcomp : (M ->ₗ[A] N) ->ₗ[A] Derivation R A M ->ₗ[A] Derivation R A N wher
e toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of a derivation with a linear map as a bilinear map
-/
def llcomp : (M →ₗ[A] N) →ₗ[A] Derivation R A M →ₗ[A] Derivation R A N where
  toFun f := f.compDer
  map_add' f₁ f₂ := by ext; rfl
  map_smul' r D := by ext; rfl

/-- Pushing a derivation forward through a linear equivalence is an equivalence. -/
/-
**Derivation._root_.LinearEquiv.compDer** 是 Mathlib 中的一个定义，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pushing a derivation forward through a linear equivalence is an equivalence.
-/
def _root_.LinearEquiv.compDer : Derivation R A M ≃ₗ[A] Derivation R A N :=
  { e.toLinearMap.compDer with
    invFun := e.symm.toLinearMap.compDer
    left_inv := fun D => by ext a; exact e.symm_apply_apply (D a)
    right_inv := fun D => by ext a; exact e.apply_symm_apply (D a) }

@[simp]
/-
**Derivation.linearEquiv_coe_to_linearMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `Deriva
tion`。
形式化陈述：linearEquiv_coe_to_linearMap_comp : (e.compDer D : A ->ₗ[R] N) = (e.toLine
arMap : M ->ₗ[R] N).comp (D : A ->ₗ[R] M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem linearEquiv_coe_to_linearMap_comp :
    (e.compDer D : A →ₗ[R] N) = (e.toLinearMap : M →ₗ[R] N).comp (D : A →ₗ[R] M) :=
  rfl

@[simp]
/-
**Derivation.linearEquiv_coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：linearEquiv_coe_comp : (e.compDer D : A -> N) = (e.toLinearMap : M ->ₗ[R] 
N).comp (D : A ->ₗ[R] M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem linearEquiv_coe_comp :
    (e.compDer D : A → N) = (e.toLinearMap : M →ₗ[R] N).comp (D : A →ₗ[R] M) :=
  rfl

end PushForward

variable (A) in
/-- For a tower `R → A → B` and an `R`-derivation `B → M`, we may compose with `A → B` to obtain an
`R`-derivation `A → M`. -/
@[simps!]
/-
**Derivation.compAlgebraMap** 是 Mathlib 中的一个定义，位于命名空间 `Derivation`。
形式化陈述：compAlgebraMap [Algebra A B] [IsScalarTower R A B] [IsScalarTower A B M] (
d : Derivation R B M) : Derivation R A M where map_one_eq_zero'
参数：d : Derivation R B M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a tower `R → A → B` and an `R`-derivation `B → M`, we may compose with `A → 
B` to obtain an
`R`-derivation `A → M`.
-/
def compAlgebraMap [Algebra A B] [IsScalarTower R A B] [IsScalarTower A B M]
    (d : Derivation R B M) : Derivation R A M where
  map_one_eq_zero' := by simp
  leibniz' a b := by simp
  toLinearMap := d.toLinearMap.comp (IsScalarTower.toAlgHom R A B).toLinearMap

variable (R A B M) in
/-- For a tower `R → A → B → M`, the precomposition defined in `compAlgebraMap`
is a `B`-linear map. -/
@[simps!]
/-
**Derivation.compAlgebraMapL** 是 Mathlib 中的一个定义，位于命名空间 `Derivation`。
形式化陈述：compAlgebraMapL [Algebra A B] [IsScalarTower R A B] [IsScalarTower A B M] 
[IsScalarTower R B M] : Derivation R B M ->ₗ[B] Derivation R A M where toFun d
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a tower `R → A → B → M`, the precomposition defined in `compAlgebraMap`
is a `B`-linear map.
-/
def compAlgebraMapL [Algebra A B] [IsScalarTower R A B] [IsScalarTower A B M]
    [IsScalarTower R B M] :
    Derivation R B M →ₗ[B] Derivation R A M where
  toFun d := d.compAlgebraMap A
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section RestrictScalars

variable {S : Type*} [CommSemiring S]
variable [Algebra S A] [Module S M] [LinearMap.CompatibleSMul A M R S]
variable (R)

/-- If `A` is both an `R`-algebra and an `S`-algebra; `M` is both an `R`-module and an `S`-module,
then an `S`-derivation `A → M` is also an `R`-derivation if it is also `R`-linear. -/
/-
**Derivation.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `Derivation`。
形式化陈述：(R : Type u_1) →   {A : Type u_2} →     {M : Type u_4} →       [inst : Com
mSemiring R] →         [inst_1 : CommSemiring A] →           [inst_2 : AddCommMo
noid M] →             [inst_3 : Algebra R A] →               [inst_4 : _root_.Mo
dule A M] →                 [inst_5 : _root_.Module R M] →                   {S 
: Type u_5} →                     [inst_6 : CommSemiring S] →                   
    [inst_7 : Algebra S A] →                         [inst_8 : _root_.Module S M
] →                           [LinearMap.CompatibleSMul A M R S] → Derivation S 
A M → Derivation R A M
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.map_one_eq_zero`：map_one_eq_zero : D 1 = 0
· 使用定理 `Derivation.leibniz`：leibniz : D (a * b) = a • D b + b • D a

--- 原说明 ---
If `A` is both an `R`-algebra and an `S`-algebra; `M` is both an `R`-module and 
an `S`-module,
then an `S`-derivation `A → M` is also an `R`-derivation if it is also `R`-linea
r.
-/
protected def restrictScalars (d : Derivation S A M) : Derivation R A M where
  map_one_eq_zero' := d.map_one_eq_zero
  leibniz' := d.leibniz
  toLinearMap := d.toLinearMap.restrictScalars R
/-
**Derivation.coe_restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 `Derivation`。
形式化陈述：coe_restrictScalars (d : Derivation S A M) : ⇑(d.restrictScalars R) = ⇑d
参数：d : Derivation S A M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_restrictScalars (d : Derivation S A M) : ⇑(d.restrictScalars R) = ⇑d := rfl

@[simp]
/-
**Derivation.restrictScalars_apply** 是 Mathlib 中的一个引理，位于命名空间 `Derivation`。
形式化陈述：restrictScalars_apply (d : Derivation S A M) (x : A) : d.restrictScalars R
 x = d x
参数：d : Derivation S A M；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalars_apply (d : Derivation S A M) (x : A) : d.restrictScalars R x = d x := rfl

end RestrictScalars

end

section Lift

variable {R : Type*} {A : Type*} {M : Type*}
variable [CommSemiring R] [CommRing A] [CommRing M]
variable [Algebra R A] [Algebra R M]
variable {F : Type*} [FunLike F A M] [AlgHomClass F R A M]

set_option backward.isDefEq.respectTransparency false in
/--
Lift a derivation via an algebra homomorphism `f` with a right inverse such that
`f(x) = 0 → f(d(x)) = 0`. This gives the derivation `f ∘ d ∘ f⁻¹`.
This is needed for an argument in [Rosenlicht, M. Integration in finite terms][Rosenlicht_1972].
-/
/-
**Derivation.liftOfRightInverse** 是 Mathlib 中的一个定义，位于命名空间 `Derivation`。
形式化陈述：liftOfRightInverse {f : F} {f_inv : M -> A} (hf : Function.RightInverse f_
inv f) ⦃d : Derivation R A A⦄ (hd : forall x, f x = 0 -> f (d x) = 0) : Derivati
on R M M where toFun x
参数：hf : Function.RightInverse f_inv f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a derivation via an algebra homomorphism `f` with a right inverse such that
`f(x) = 0 → f(d(x)) = 0`. This gives the derivation `f ∘ d ∘ f⁻¹`.
This is needed for an argument in [Rosenlicht, M. Integration in finite terms][R
osenlicht_1972].
-/
def liftOfRightInverse {f : F} {f_inv : M → A} (hf : Function.RightInverse f_inv f)
    ⦃d : Derivation R A A⦄ (hd : ∀ x, f x = 0 → f (d x) = 0) : Derivation R M M where
  toFun x := f (d (f_inv x))
  map_add' x y := by
    suffices f (d (f_inv (x + y) - (f_inv x + f_inv y))) = 0 by simpa [sub_eq_zero]
    apply hd
    simp [hf _]
  map_smul' x y := by
    suffices f (d (f_inv (x • y) - x • f_inv y)) = 0 by simpa [sub_eq_zero]
    apply hd
    simp [hf _]
  map_one_eq_zero' := by
    suffices f (d (f_inv 1 - 1)) = 0 by simpa [sub_eq_zero]
    apply hd
    simp [hf _]
  leibniz' x y := by
    suffices f (d (f_inv (x * y) - f_inv x * f_inv y)) = 0 by simpa [sub_eq_zero, hf _]
    apply hd
    simp [hf _]

@[simp]
/-
**Derivation.liftOfRightInverse_apply** 是 Mathlib 中的一个引理，位于命名空间 `Derivation`。
形式化陈述：liftOfRightInverse_apply {f : F} {f_inv : M -> A} (hf : Function.RightInve
rse f_inv f) {d : Derivation R A A} (hd : forall x, f x = 0 -> f (d x) = 0) (x :
 A) : Derivation.liftOfRightInverse hf hd (f x) = f (d x)
参数：hf : Function.RightInverse f_inv f；hd : forall x, f x = 0 -> f (d x) = 0；x : 
A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
-/
lemma liftOfRightInverse_apply {f : F} {f_inv : M → A} (hf : Function.RightInverse f_inv f)
    {d : Derivation R A A} (hd : ∀ x, f x = 0 → f (d x) = 0) (x : A) :
    Derivation.liftOfRightInverse hf hd (f x) = f (d x) := by
  suffices f (d (f_inv (f x) - x)) = 0 by simpa [sub_eq_zero]
  apply hd
  simp [hf _]
/-
**Derivation.liftOfRightInverse_eq** 是 Mathlib 中的一个引理，位于命名空间 `Derivation`。
形式化陈述：liftOfRightInverse_eq {f : F} {f_inv₁ f_inv₂ : M -> A} (hf₁ : Function.Rig
htInverse f_inv₁ f) (hf₂ : Function.RightInverse f_inv₂ f) : liftOfRightInverse 
hf₁ = liftOfRightInverse hf₂
参数：hf₁ : Function.RightInverse f_inv₁ f；hf₂ : Function.RightInverse f_inv₂ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Derivation.ext`：ext (H : forall a, D1 a = D2 a) : D1 = D2
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Derivation.liftOfRightInverse_apply`：liftOfRightInverse_apply {f : F} {f
_inv : M -> A} (hf : Function.RightInverse f_inv f) {d : Derivation R A A} (hd :
 forall x, f x = 0 -> f (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma liftOfRightInverse_eq {f : F} {f_inv₁ f_inv₂ : M → A} (hf₁ : Function.RightInverse f_inv₁ f)
    (hf₂ : Function.RightInverse f_inv₂ f) :
    liftOfRightInverse hf₁ = liftOfRightInverse hf₂ := by
  ext _ _ x
  obtain ⟨x, rfl⟩ := hf₁.surjective x
  simp

/--
A noncomputable version of `liftOfRightInverse` for surjective homomorphisms.
-/
/-
**Derivation.liftOfSurjective** 是 Mathlib 中的一个缩写定义，位于命名空间 `Derivation`。
形式化陈述：liftOfSurjective {f : F} (hf : Function.Surjective f) ⦃d : Derivation R A 
A⦄ (hd : forall x, f x = 0 -> f (d x) = 0) : Derivation R M M
参数：hf : Function.Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A noncomputable version of `liftOfRightInverse` for surjective homomorphisms.
-/
noncomputable abbrev liftOfSurjective {f : F} (hf : Function.Surjective f)
    ⦃d : Derivation R A A⦄ (hd : ∀ x, f x = 0 → f (d x) = 0) : Derivation R M M :=
  d.liftOfRightInverse (Function.rightInverse_surjInv hf) hd
/-
**Derivation.liftOfSurjective_apply** 是 Mathlib 中的一个引理，位于命名空间 `Derivation`。
形式化陈述：liftOfSurjective_apply {f : F} (hf : Function.Surjective f) {d : Derivatio
n R A A} (hd : forall x, f x = 0 -> f (d x) = 0) (x : A) : Derivation.liftOfSurj
ective hf hd (f x) = f (d x)
参数：hf : Function.Surjective f；hd : forall x, f x = 0 -> f (d x) = 0；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Derivation.liftOfRightInverse_apply`：liftOfRightInverse_apply {f : F} {f
_inv : M -> A} (hf : Function.RightInverse f_inv f) {d : Derivation R A A} (hd :
 forall x, f x = 0 -> f (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma liftOfSurjective_apply {f : F} (hf : Function.Surjective f)
    {d : Derivation R A A} (hd : ∀ x, f x = 0 → f (d x) = 0) (x : A) :
    Derivation.liftOfSurjective hf hd (f x) = f (d x) := by simp

end Lift

section Cancel

variable {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [Algebra R A] {M : Type*}
  [AddCancelCommMonoid M] [Module R M] [Module A M]

/-- Define `Derivation R A M` from a linear map when `M` is cancellative by verifying the Leibniz
rule. -/
/-
**Derivation.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Derivation`。
形式化陈述：mk' (D : A ->ₗ[R] M) (h : forall a b, D (a * b) = a • D b + b • D a) : Der
ivation R A M where toLinearMap
参数：D : A ->ₗ[R] M；h : forall a b, D (a * b) = a • D b + b • D a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define `Derivation R A M` from a linear map when `M` is cancellative by verifyin
g the Leibniz
rule.
-/
def mk' (D : A →ₗ[R] M) (h : ∀ a b, D (a * b) = a • D b + b • D a) : Derivation R A M where
  toLinearMap := D
  map_one_eq_zero' := (add_eq_left (a := D 1)).1 <| by
    simpa only [one_smul, one_mul] using (h 1 1).symm
  leibniz' := h

@[simp]
/-
**Derivation.coe_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：coe_mk' (D : A ->ₗ[R] M) (h) : ⇑(mk' D h) = D
参数：D : A ->ₗ[R] M；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk' (D : A →ₗ[R] M) (h) : ⇑(mk' D h) = D :=
  rfl

@[simp]
/-
**Derivation.coe_mk'_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {A : Type u_2} [inst_1 : CommSemi
ring A] [inst_2 : Algebra R A] {M : Type u_3}   [inst_3 : AddCancelCommMonoid M]
 [inst_4 : _root_.Module R M] [inst_5 : _root_.Module A M] (D : A →ₗ[R] M)   (h 
: ∀ (a b : A), D (a * b) = a • D b + b • D a), ↑(Derivation.mk' D h) = D
参数：D : A →ₗ[R] M；h : ∀ (a b : A), D (a * b) = a • D b + b • D a；Derivation.mk' D
 h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk'_linearMap (D : A →ₗ[R] M) (h) : (mk' D h : A →ₗ[R] M) = D :=
  rfl

end Cancel

section

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]

section

variable {M : Type*} [AddCommGroup M] [Module A M] [Module R M]
variable (D : Derivation R A M) {D1 D2 : Derivation R A M} (r : R) (a b : A)

/-
**Derivation.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {A : Type u_2} [inst_1 : CommRing A] 
[inst_2 : Algebra R A] {M : Type u_3}   [inst_3 : AddCommGroup M] [inst_4 : _roo
t_.Module A M] [inst_5 : _root_.Module R M] (D : Derivation R A M) (a : A),   D 
(-a) = -D a
参数：D : Derivation R A M；a : A；-a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
-/
protected theorem map_neg : D (-a) = -D a :=
  map_neg D a
/-
**Derivation.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {A : Type u_2} [inst_1 : CommRing A] 
[inst_2 : Algebra R A] {M : Type u_3}   [inst_3 : AddCommGroup M] [inst_4 : _roo
t_.Module A M] [inst_5 : _root_.Module R M] (D : Derivation R A M) (a b : A),   
D (a - b) = D a - D b
参数：D : Derivation R A M；a b : A；a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
-/
protected theorem map_sub : D (a - b) = D a - D b :=
  map_sub D a b

@[simp]
/-
**Derivation.map_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：map_intCast (n : Int) : D (n : A) = 0
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
· 使用定理 `Derivation.map_smul_of_tower`：map_smul_of_tower {S : Type*} [SMul S A] [
SMul S M] [LinearMap.CompatibleSMul A M S R] (D : Derivation R A M) (r : S) (a :
 A) : D (r • a) = …
· 使用定理 `LinearMap.CompatibleSMul.intModule`：∀ {M : Type u_8} {M₂ : Type u_10} [i
nst : AddCommGroup M] [inst_1 : AddCommGroup M₂] {S : Type u_14}   [inst_2 : Sem
iring S] [inst_3 : _root…
· 使用定理 `Derivation.map_one_eq_zero`：map_one_eq_zero : D 1 = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem map_intCast (n : ℤ) : D (n : A) = 0 := by
  rw [← zsmul_one, D.map_smul_of_tower n, map_one_eq_zero, smul_zero]
/-
**Derivation.leibniz_of_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：leibniz_of_mul_eq_one {a b : A} (h : a * b = 1) : D a = -a ^ 2 • D b
参数：h : a * b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `eq_neg_of_add_eq_zero_left`：∀ {G : Type u_1} [inst : SubtractionMonoid G
] {a b : G}, a + b = 0 → a = -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Derivation.leibniz`：leibniz : D (a * b) = a • D b + b • D a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Derivation.map_one_eq_zero`：map_one_eq_zero : D 1 = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem leibniz_of_mul_eq_one {a b : A} (h : a * b = 1) : D a = -a ^ 2 • D b := by
  rw [neg_smul]
  refine eq_neg_of_add_eq_zero_left ?_
  calc
    D a + a ^ 2 • D b = a • b • D a + a • a • D b := by simp only [smul_smul, h, one_smul, sq]
    _ = a • D (a * b) := by rw [leibniz, smul_add, add_comm]
    _ = 0 := by rw [h, map_one_eq_zero, smul_zero]
/-
**Derivation.leibniz_invOf** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：leibniz_invOf [Invertible a] : D (⅟a) = -⅟a ^ 2 • D a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.leibniz_of_mul_eq_one`：leibniz_of_mul_eq_one {a b : A} (h : a
 * b = 1) : D a = -a ^ 2 • D b
· 使用定理 `invOf_mul_self`：invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : 
⅟a * a = 1
-/
theorem leibniz_invOf [Invertible a] : D (⅟a) = -⅟a ^ 2 • D a :=
  D.leibniz_of_mul_eq_one <| invOf_mul_self a

section Field

variable {K : Type*} [Field K] [Module K M] [Algebra R K] (D : Derivation R K M)

/-
**Derivation.leibniz_inv** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：leibniz_inv (a : K) : D a⁻¹ = -a⁻¹ ^ 2 • D a
参数：a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Derivation.leibniz_of_mul_eq_one`：leibniz_of_mul_eq_one {a b : A} (h : a
 * b = 1) : D a = -a ^ 2 • D b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
-/
theorem leibniz_inv (a : K) : D a⁻¹ = -a⁻¹ ^ 2 • D a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  · exact D.leibniz_of_mul_eq_one (inv_mul_cancel₀ ha)
/-
**Derivation.leibniz_div** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：leibniz_div (a b : K) : D (a / b) = b⁻¹ ^ 2 • (b • D a - a • D b)
参数：a b : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Derivation.leibniz`：leibniz : D (a * b) = a • D b + b • D a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Derivation.leibniz_inv`：leibniz_inv (a : K) : D a⁻¹ = -a⁻¹ ^ 2 • D a
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_mul_self`：inv_mul_mul_self (a : G₀) : a⁻¹ * a * a = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_inv_one`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {a : α}, Mathlib.Meta.NormNum.IsNat a 1 → Mathlib.Meta.NormNum.IsNat a⁻
¹ 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 52 条，此处仅展示前 30 条）
-/
theorem leibniz_div (a b : K) : D (a / b) = b⁻¹ ^ 2 • (b • D a - a • D b) := by
  simp only [div_eq_mul_inv, leibniz, leibniz_inv, inv_pow, neg_smul, smul_neg, smul_smul, add_comm,
    sub_eq_add_neg, smul_add]
  rw [← inv_mul_mul_self b⁻¹, inv_inv]
  ring_nf
/-
**Derivation.leibniz_div_const** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：leibniz_div_const (a b : K) (h : D b = 0) : D (a / b) = b⁻¹ • D a
参数：a b : K；h : D b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Derivation.leibniz_div`：leibniz_div (a b : K) : D (a / b) = b⁻¹ ^ 2 • (b
 • D a - a • D b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_self_mul_inv`：mul_self_mul_inv (a : G₀) : a * a * a⁻¹ = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
（共 47 条，此处仅展示前 30 条）
-/
theorem leibniz_div_const (a b : K) (h : D b = 0) : D (a / b) = b⁻¹ • D a := by
  simp only [leibniz_div, inv_pow, h, smul_zero, sub_zero, smul_smul]
  rw [← mul_self_mul_inv b⁻¹, inv_inv]
  ring_nf
/-
**Derivation.leibniz_zpow** 是 Mathlib 中的一个引理，位于命名空间 `Derivation`。
形式化陈述：leibniz_zpow (a : K) (n : Int) : D (a ^ n) = n • a ^ (n - 1) • D a
参数：a : K；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Derivation.map_one_eq_zero`：map_one_eq_zero : D 1 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_zpow`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀] (n : ℤ), n ≠ 0 → 
0 ^ n = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Int.natAbs_eq`：∀ (a : ℤ), a = ↑a.natAbs ∨ a = -↑a.natAbs
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Derivation.leibniz_pow`：leibniz_pow (n : Nat) : D (a ^ n) = n • a ^ (n -
 1) • D a
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Derivation.leibniz_inv`：leibniz_inv (a : K) : D a⁻¹ = -a⁻¹ ^ 2 • D a
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
（共 66 条，此处仅展示前 30 条）
-/
lemma leibniz_zpow (a : K) (n : ℤ) : D (a ^ n) = n • a ^ (n - 1) • D a := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases ha : a = 0
  · simp [ha, zero_zpow n hn]
  rcases Int.natAbs_eq n with h | h
  · rw [h]
    simp only [zpow_natCast, leibniz_pow, natCast_zsmul]
    rw [← zpow_natCast]
    congr
    lia
  · rw [h, zpow_neg, zpow_natCast, leibniz_inv, leibniz_pow, inv_pow, ← pow_mul, ← zpow_natCast,
      ← zpow_natCast, ← Nat.cast_smul_eq_nsmul K, ← Int.cast_smul_eq_zsmul K, smul_smul, smul_smul,
      smul_smul]
    trans (-n.natAbs * (a ^ ((n.natAbs - 1 : ℕ) : ℤ) / (a ^ ((n.natAbs * 2 : ℕ) : ℤ)))) • D a
    · ring_nf
    rw [← zpow_sub₀ ha]
    congr 3
    · norm_cast
    lia

end Field

/-
**Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (Derivation R A M) :=
  ⟨fun D =>
    mk' (-D) fun a b => by
      simp only [LinearMap.neg_apply, smul_neg, neg_add_rev, leibniz, coeFn_coe, add_comm]⟩

@[simp]
/-
**Derivation.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：coe_neg (D : Derivation R A M) : ⇑(-D) = -D
参数：D : Derivation R A M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (D : Derivation R A M) : ⇑(-D) = -D :=
  rfl

@[simp]
/-
**Derivation.coe_neg_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：coe_neg_linearMap (D : Derivation R A M) : ↑(-D) = (-D : A ->ₗ[R] M)
参数：D : Derivation R A M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg_linearMap (D : Derivation R A M) : ↑(-D) = (-D : A →ₗ[R] M) :=
  rfl
/-
**Derivation.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：neg_apply : (-D) a = -D a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply : (-D) a = -D a :=
  rfl
/-
**Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (Derivation R A M) :=
  ⟨fun D1 D2 =>
    mk' (D1 - D2 : A →ₗ[R] M) fun a b => by
      simp only [LinearMap.sub_apply, leibniz, coeFn_coe, smul_sub, add_sub_add_comm]⟩

@[simp]
/-
**Derivation.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：coe_sub (D1 D2 : Derivation R A M) : ⇑(D1 - D2) = D1 - D2
参数：D1 D2 : Derivation R A M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub (D1 D2 : Derivation R A M) : ⇑(D1 - D2) = D1 - D2 :=
  rfl

@[simp]
/-
**Derivation.coe_sub_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：coe_sub_linearMap (D1 D2 : Derivation R A M) : ↑(D1 - D2) = (D1 - D2 : A -
>ₗ[R] M)
参数：D1 D2 : Derivation R A M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub_linearMap (D1 D2 : Derivation R A M) : ↑(D1 - D2) = (D1 - D2 : A →ₗ[R] M) :=
  rfl
/-
**Derivation.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：sub_apply : (D1 - D2) a = D1 a - D2 a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply : (D1 - D2) a = D1 a - D2 a :=
  rfl
/-
**Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (Derivation R A M) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

end

end

end Derivation

