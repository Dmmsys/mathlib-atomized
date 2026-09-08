/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Bilinear form

This file defines a bilinear form over a module. Basic ideas
such as orthogonality are also introduced, as well as reflexive,
symmetric, non-degenerate and alternating bilinear forms. Adjoints of
linear maps with respect to a bilinear form are also introduced.

A bilinear form on an `R`-(semi)module `M`, is a function from `M × M` to `R`,
that is linear in both arguments. Comments will typically abbreviate
"(semi)module" as just "module", but the definitions should be as general as
possible.

The result that there exists an orthogonal basis with respect to a symmetric,
nondegenerate bilinear form can be found in `QuadraticForm.lean` with
`exists_orthogonal_basis`.

## Notation

Given any term `B` of type `BilinForm`, due to a coercion, can use
the notation `B x y` to refer to the function field, i.e. `B x y = B.bilin x y`.

In this file we use the following type variables:
- `M`, `M'`, ... are modules over the commutative semiring `R`,
- `M₁`, `M₁'`, ... are modules over the commutative ring `R₁`,
- `V`, ... is a vector space over the field `K`.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/

@[expose] public section

export LinearMap (BilinForm)

open LinearMap (BilinForm)

universe u v w

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]
variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]
variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

/-
**LinearMap.BilinForm.add_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：add_left (x y z : M) : B (x + y) z = B x z + B y z
参数：x y z : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_add₂`：map_add₂ (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (x₁ x₂ y) :
 f (x₁ + x₂) y = f x₁ y + f x₂ y
-/
theorem add_left (x y z : M) : B (x + y) z = B x z + B y z := map_add₂ _ _ _ _
/-
**LinearMap.BilinForm.smul_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：smul_left (a : R) (x y : M) : B (a • x) y = a * B x y
参数：a : R；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_smul₂`：map_smul₂ (f : M₂ ->ₗ[R] N₂ ->ₛₗ[σ₁₂] P₂) (r : R) (
x y) : f (r • x) y = r • f x y
-/
theorem smul_left (a : R) (x y : M) : B (a • x) y = a * B x y := map_smul₂ _ _ _ _
/-
**LinearMap.BilinForm.add_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：add_right (x y z : M) : B x (y + z) = B x y + B x z
参数：x y z : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
theorem add_right (x y z : M) : B x (y + z) = B x y + B x z := map_add _ _ _
/-
**LinearMap.BilinForm.smul_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：smul_right (a : R) (x y : M) : B x (a • y) = a * B x y
参数：a : R；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
theorem smul_right (a : R) (x y : M) : B x (a • y) = a * B x y := map_smul _ _ _
/-
**LinearMap.BilinForm.zero_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：zero_left (x : M) : B 0 x = 0
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_zero₂`：map_zero₂ (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (y) : f 0
 y = 0
-/
theorem zero_left (x : M) : B 0 x = 0 := map_zero₂ _ _
/-
**LinearMap.BilinForm.zero_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：zero_right (x : M) : B x 0 = 0
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem zero_right (x : M) : B x 0 = 0 := map_zero _
/-
**LinearMap.BilinForm.neg_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：neg_left (x y : M₁) : B₁ (-x) y = -B₁ x y
参数：x y : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_neg₂`：map_neg₂ (f : M' ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P') (x y) : f
 (-x) y = -f x y
-/
theorem neg_left (x y : M₁) : B₁ (-x) y = -B₁ x y := map_neg₂ _ _ _
/-
**LinearMap.BilinForm.neg_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：neg_right (x y : M₁) : B₁ x (-y) = -B₁ x y
参数：x y : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem neg_right (x y : M₁) : B₁ x (-y) = -B₁ x y := map_neg _ _
/-
**LinearMap.BilinForm.sub_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：sub_left (x y z : M₁) : B₁ (x - y) z = B₁ x z - B₁ y z
参数：x y z : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_sub₂`：map_sub₂ (f : M' ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P') (x y z) :
 f (x - y) z = f x z - f y z
-/
theorem sub_left (x y z : M₁) : B₁ (x - y) z = B₁ x z - B₁ y z := map_sub₂ _ _ _ _
/-
**LinearMap.BilinForm.sub_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：sub_right (x y z : M₁) : B₁ x (y - z) = B₁ x y - B₁ x z
参数：x y z : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem sub_right (x y z : M₁) : B₁ x (y - z) = B₁ x y - B₁ x z := map_sub _ _ _
/-
**LinearMap.BilinForm.smul_left_of_tower** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.Bi
linForm`。
形式化陈述：smul_left_of_tower (r : S) (x y : M) : B (r • x) y = r • B x y
参数：r : S；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_smul`：algebraMap_smul [SMul R M] [IsScalarTower
 R A M] (r : R) (x : M) : algebraMap R A r • x = r • x
· 使用定理 `LinearMap.BilinForm.smul_left`：smul_left (a : R) (x y : M) : B (a • x) y
 = a * B x y
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
lemma smul_left_of_tower (r : S) (x y : M) : B (r • x) y = r • B x y := by
  rw [← IsScalarTower.algebraMap_smul R r, smul_left, Algebra.smul_def]
/-
**LinearMap.BilinForm.smul_right_of_tower** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.B
ilinForm`。
形式化陈述：smul_right_of_tower (r : S) (x y : M) : B x (r • y) = r • B x y
参数：r : S；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_smul`：algebraMap_smul [SMul R M] [IsScalarTower
 R A M] (r : R) (x : M) : algebraMap R A r • x = r • x
· 使用定理 `LinearMap.BilinForm.smul_right`：smul_right (a : R) (x y : M) : B x (a • 
y) = a * B x y
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
lemma smul_right_of_tower (r : S) (x y : M) : B x (r • y) = r • B x y := by
  rw [← IsScalarTower.algebraMap_smul R r, smul_right, Algebra.smul_def]

variable {D : BilinForm R M} {D₁ : BilinForm R₁ M₁}

-- TODO: instantiate `FunLike`
/-
**LinearMap.BilinForm.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinFo
rm`。
形式化陈述：coe_injective : Function.Injective ((fun B x y => B x y) : BilinForm R M -
> M -> M -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrFun₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort
 u_3} {f g : (a : α) → (b : β a) → γ a b},   f = g → ∀ (a : α) (b : β a), f a b…
-/
theorem coe_injective : Function.Injective ((fun B x y => B x y) : BilinForm R M → M → M → R) :=
  fun B D h => by
    ext x y
    apply congrFun₂ h

@[ext]
/-
**LinearMap.BilinForm.ext** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：ext (H : forall x y : M, B x y = D x y) : B = D
参数：H : forall x y : M, B x y = D x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext₂`：ext₂ {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (H : forall m n, 
f m n = g m n) : f = g
-/
theorem ext (H : ∀ x y : M, B x y = D x y) : B = D := ext₂ H
/-
**LinearMap.BilinForm.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：congr_fun (h : B = D) (x y : M) : B x y = D x y
参数：h : B = D；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun₂`：congr_fun₂ {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (h : 
f = g) (x y) : f x y = g x y
-/
theorem congr_fun (h : B = D) (x y : M) : B x y = D x y := congr_fun₂ h _ _

@[simp]
/-
**LinearMap.BilinForm.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：zero_apply (x y : M) : (0 : BilinForm R M) x y = 0
参数：x y : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (x y : M) : (0 : BilinForm R M) x y = 0 :=
  rfl

variable (B D B₁ D₁)

@[simp]
/-
**LinearMap.BilinForm.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：add_apply (x y : M) : (B + D) x y = B x y + D x y
参数：x y : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply (x y : M) : (B + D) x y = B x y + D x y :=
  rfl

@[simp]
/-
**LinearMap.BilinForm.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：neg_apply (x y : M₁) : (-B₁) x y = -B₁ x y
参数：x y : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply (x y : M₁) : (-B₁) x y = -B₁ x y :=
  rfl

@[simp]
/-
**LinearMap.BilinForm.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：sub_apply (x y : M₁) : (B₁ - D₁) x y = B₁ x y - D₁ x y
参数：x y : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply (x y : M₁) : (B₁ - D₁) x y = B₁ x y - D₁ x y :=
  rfl

/-- `coeFn` as an `AddMonoidHom` -/
@[simps]
/-
**LinearMap.BilinForm.coeFnAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.Bil
inForm`。
形式化陈述：coeFnAddMonoidHom : BilinForm R M ->+ M -> M -> R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`coeFn` as an `AddMonoidHom`
-/
def coeFnAddMonoidHom : BilinForm R M →+ M → M → R where
  toFun := fun B x y => B x y
  map_zero' := rfl
  map_add' _ _ := rfl

section flip

/-- The flip of a bilinear form, obtained by exchanging the left and right arguments. -/
/-
**LinearMap.BilinForm.flipHom** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：flipHom : BilinForm R M ≃ₗ[R] BilinForm R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The flip of a bilinear form, obtained by exchanging the left and right arguments
.
-/
def flipHom : BilinForm R M ≃ₗ[R] BilinForm R M := LinearMap.lflip

@[simp]
/-
**LinearMap.BilinForm.flip_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：flip_apply (A : BilinForm R M) (x y : M) : flipHom A x y = A y x
参数：A : BilinForm R M；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem flip_apply (A : BilinForm R M) (x y : M) : flipHom A x y = A y x :=
  rfl
/-
**LinearMap.BilinForm.flip_flip** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：flip_flip : flipHom.trans flipHom = LinearEquiv.refl R (BilinForm R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem flip_flip :
    flipHom.trans flipHom = LinearEquiv.refl R (BilinForm R M) := by
  ext A
  simp

/-- The `flip` of a bilinear form over a commutative ring, obtained by exchanging the left and
right arguments. -/
/-
**LinearMap.BilinForm.flip** 是 Mathlib 中的一个缩写定义，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：flip (B : BilinForm R M)
参数：B : BilinForm R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `flip` of a bilinear form over a commutative ring, obtained by exchanging th
e left and
right arguments.
-/
abbrev flip (B : BilinForm R M) :=
  flipHom B

end flip

/-- The restriction of a bilinear form on a submodule. -/
@[simps! apply]
/-
**LinearMap.BilinForm.restrict** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：restrict (B : BilinForm R M) (W : Submodule R M) : BilinForm R W
参数：B : BilinForm R M；W : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a bilinear form on a submodule.
-/
def restrict (B : BilinForm R M) (W : Submodule R M) : BilinForm R W :=
  LinearMap.domRestrict₁₂ B W W

end BilinForm

@[simp]
/-
**LinearMap.lsmul_flip_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lsmul_flip_apply (m : M) : (lsmul R M).flip m = toSpanSingleton R M m
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
theorem lsmul_flip_apply (m : M) : (lsmul R M).flip m = toSpanSingleton R M m := rfl

end LinearMap

