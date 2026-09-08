/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Graded.External
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Tactic.SuppressCompilation

/-!
# Graded tensor products over graded algebras

The graded tensor product $A \hat\otimes_R B$ is imbued with a multiplication defined on homogeneous
tensors by:

$$(a \otimes b) \cdot (a' \otimes b') = (-1)^{\deg a' \deg b} (a \cdot a') \otimes (b \cdot b')$$

where $A$ and $B$ are algebras graded by `ℕ`, `ℤ`, or `ι` (or more generally, any index
that satisfies `Module ι (Additive ℤˣ)`).

## Main results

* `GradedTensorProduct R 𝒜 ℬ`: for families of submodules of `A` and `B` that form a graded algebra,
  this is a type alias for `A ⊗[R] B` with the appropriate multiplication.
* `GradedTensorProduct.instAlgebra`: the ring structure induced by this multiplication.
* `GradedTensorProduct.liftEquiv`: a universal property for graded tensor products

## Notation

* `𝒜 ᵍ⊗[R] ℬ` is notation for `GradedTensorProduct R 𝒜 ℬ`.
* `a ᵍ⊗ₜ b` is notation for `GradedTensorProduct.tmul _ a b`.

## References

* https://math.stackexchange.com/q/202718/1896
* [*Algebra I*, Bourbaki : Chapter III, §4.7, example (2)][bourbaki1989]

## Implementation notes

We cannot put the multiplication on `A ⊗[R] B` directly as it would conflict with the existing
multiplication defined without the $(-1)^{\deg a' \deg b}$ term. Furthermore, the ring `A` may not
have a unique graduation, and so we need the chosen graduation `𝒜` to appear explicitly in the
type.

## TODO

* Show that the tensor product of graded algebras is itself a graded algebra.
* Determine if replacing the synonym with a single-field structure improves performance.
-/

@[expose] public section

suppress_compilation

open scoped TensorProduct

variable {R ι A B : Type*}
variable [CommSemiring ι] [DecidableEq ι]
variable [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
variable (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

open DirectSum


variable (R) in
/-- A Type synonym for `A ⊗[R] B`, but with multiplication as `TensorProduct.gradedMul`.

This has notation `𝒜 ᵍ⊗[R] ℬ`. -/
@[nolint unusedArguments]
/-
**GradedTensorProduct** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GradedTensorProduct (𝒜 : ι -> Submodule R A) (ℬ : ι -> Submodule R B) [Gra
dedAlgebra 𝒜] [GradedAlgebra ℬ] : Type _
参数：𝒜 : ι -> Submodule R A；ℬ : ι -> Submodule R B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Type synonym for `A ⊗[R] B`, but with multiplication as `TensorProduct.gradedM
ul`.

This has notation `𝒜 ᵍ⊗[R] ℬ`.
-/
def GradedTensorProduct
    (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] :
    Type _ :=
  A ⊗[R] B
deriving AddCommGroupWithOne, Module R

namespace GradedTensorProduct

open TensorProduct

@[inherit_doc GradedTensorProduct]
scoped[TensorProduct] notation:100 𝒜 " ᵍ⊗[" R "] " ℬ:100 => GradedTensorProduct R 𝒜 ℬ

variable (R) in
/-- The casting equivalence to move between regular and graded tensor products. -/
/-
**GradedTensorProduct.of** 是 Mathlib 中的一个定义，位于命名空间 `GradedTensorProduct`。
形式化陈述：of : A otimes[R] B ≃ₗ[R] 𝒜 ᵍotimes[R] ℬ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The casting equivalence to move between regular and graded tensor products.
-/
def of : A ⊗[R] B ≃ₗ[R] 𝒜 ᵍ⊗[R] ℬ := LinearEquiv.refl _ _

@[simp]
/-
**GradedTensorProduct.of_one** 是 Mathlib 中的一个定理，位于命名空间 `GradedTensorProduct`。
形式化陈述：of_one : of R 𝒜 ℬ 1 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_one : of R 𝒜 ℬ 1 = 1 := rfl

@[simp]
/-
**GradedTensorProduct.of_symm_one** 是 Mathlib 中的一个定理，位于命名空间 `GradedTensorProduct
`。
形式化陈述：of_symm_one : (of R 𝒜 ℬ).symm 1 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_symm_one : (of R 𝒜 ℬ).symm 1 = 1 := rfl

@[simp]
/-
**GradedTensorProduct.of_symm_of** 是 Mathlib 中的一个定理，位于命名空间 `GradedTensorProduct`
。
形式化陈述：of_symm_of (x : A otimes[R] B) : (of R 𝒜 ℬ).symm (of R 𝒜 ℬ x) = x
参数：x : A otimes[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_symm_of (x : A ⊗[R] B) : (of R 𝒜 ℬ).symm (of R 𝒜 ℬ x) = x := rfl

@[simp]
/-
**GradedTensorProduct.symm_of_of** 是 Mathlib 中的一个定理，位于命名空间 `GradedTensorProduct`
。
形式化陈述：symm_of_of (x : 𝒜 ᵍotimes[R] ℬ) : of R 𝒜 ℬ ((of R 𝒜 ℬ).symm x) = x
参数：x : 𝒜 ᵍotimes[R] ℬ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_of_of (x : 𝒜 ᵍ⊗[R] ℬ) : of R 𝒜 ℬ ((of R 𝒜 ℬ).symm x) = x := rfl

/-- Two linear maps from the graded tensor product agree if they agree on the underlying tensor
product. -/
@[ext]
/-
**GradedTensorProduct.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `GradedTensorProduct`。
形式化陈述：hom_ext {M} [AddCommMonoid M] [Module R M] ⦃f g : 𝒜 ᵍotimes[R] ℬ ->ₗ[R] M⦄
 (h : f ∘ₗ of R 𝒜 ℬ = (g ∘ₗ of R 𝒜 ℬ : A otimes[R] B ->ₗ[R] M)) : f = g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two linear maps from the graded tensor product agree if they agree on the underl
ying tensor
product.
-/
theorem hom_ext {M} [AddCommMonoid M] [Module R M] ⦃f g : 𝒜 ᵍ⊗[R] ℬ →ₗ[R] M⦄
    (h : f ∘ₗ of R 𝒜 ℬ = (g ∘ₗ of R 𝒜 ℬ : A ⊗[R] B →ₗ[R] M)) :
    f = g :=
  h

variable (R) {𝒜 ℬ} in
/-- The graded tensor product of two elements of graded rings. -/
/-
**GradedTensorProduct.tmul** 是 Mathlib 中的一个缩写定义，位于命名空间 `GradedTensorProduct`。
形式化陈述：tmul (a : A) (b : B) : 𝒜 ᵍotimes[R] ℬ
参数：a : A；b : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The graded tensor product of two elements of graded rings.
-/
abbrev tmul (a : A) (b : B) : 𝒜 ᵍ⊗[R] ℬ := of R 𝒜 ℬ (a ⊗ₜ b)

@[inherit_doc]
notation:100 x " ᵍ⊗ₜ " y:100 => tmul _ x y

@[inherit_doc]
notation:100 x " ᵍ⊗ₜ[" R "] " y:100 => tmul R x y

variable (R) in
/-- An auxiliary construction to move between the graded tensor product of internally-graded objects
and the tensor product of direct sums. -/
/-
**GradedTensorProduct.auxEquiv** 是 Mathlib 中的一个定义，位于命名空间 `GradedTensorProduct`。
形式化陈述：auxEquiv : (𝒜 ᵍotimes[R] ℬ) ≃ₗ[R] (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary construction to move between the graded tensor product of internall
y-graded objects
and the tensor product of direct sums.
-/
noncomputable def auxEquiv : (𝒜 ᵍ⊗[R] ℬ) ≃ₗ[R] (⨁ i, 𝒜 i) ⊗[R] (⨁ i, ℬ i) :=
  let fA := (decomposeAlgEquiv 𝒜).toLinearEquiv
  let fB := (decomposeAlgEquiv ℬ).toLinearEquiv
  (of R 𝒜 ℬ).symm.trans (TensorProduct.congr fA fB)
/-
**GradedTensorProduct.auxEquiv_tmul** 是 Mathlib 中的一个定理，位于命名空间 `GradedTensorProdu
ct`。
形式化陈述：auxEquiv_tmul (a : A) (b : B) : auxEquiv R 𝒜 ℬ (a ᵍotimesₜ b) = decompose 
𝒜 a otimesₜ decompose ℬ b
参数：a : A；b : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem auxEquiv_tmul (a : A) (b : B) :
    auxEquiv R 𝒜 ℬ (a ᵍ⊗ₜ b) = decompose 𝒜 a ⊗ₜ decompose ℬ b := rfl
/-
**GradedTensorProduct.auxEquiv_one** 是 Mathlib 中的一个定理，位于命名空间 `GradedTensorProduc
t`。
形式化陈述：auxEquiv_one : auxEquiv R 𝒜 ℬ 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GradedTensorProduct.of_one`：of_one : of R 𝒜 ℬ 1 = 1
· 使用定理 `Algebra.TensorProduct.one_def`：one_def : (1 : A otimes[R] B) = (1 : A) o
timesₜ (1 : B)
· 使用定理 `GradedTensorProduct.auxEquiv_tmul`：auxEquiv_tmul (a : A) (b : B) : auxEq
uiv R 𝒜 ℬ (a ᵍotimesₜ b) = decompose 𝒜 a otimesₜ decompose ℬ b
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `DirectSum.decompose_one`：decompose_one : decompose 𝒜 (1 : A) = 1
-/
theorem auxEquiv_one : auxEquiv R 𝒜 ℬ 1 = 1 := by
  rw [← of_one, Algebra.TensorProduct.one_def, auxEquiv_tmul 𝒜 ℬ, DirectSum.decompose_one,
    DirectSum.decompose_one, Algebra.TensorProduct.one_def]
/-
**GradedTensorProduct.auxEquiv_symm_one** 是 Mathlib 中的一个定理，位于命名空间 `GradedTensorP
roduct`。
形式化陈述：auxEquiv_symm_one : (auxEquiv R 𝒜 ℬ).symm 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GradedTensorProduct.auxEquiv_one`：auxEquiv_one : auxEquiv R 𝒜 ℬ 1 = 1
-/
theorem auxEquiv_symm_one : (auxEquiv R 𝒜 ℬ).symm 1 = 1 :=
  (LinearEquiv.symm_apply_eq _).mpr (auxEquiv_one _ _).symm

variable [Module ι (Additive ℤˣ)]

/-- Auxiliary construction used to build the `Mul` instance and get distributivity of `+` and
`\smul`. -/
/-
**GradedTensorProduct.mulHom** 是 Mathlib 中的一个定义，位于命名空间 `GradedTensorProduct`。
形式化陈述：mulHom : (𝒜 ᵍotimes[R] ℬ) ->ₗ[R] (𝒜 ᵍotimes[R] ℬ) ->ₗ[R] (𝒜 ᵍotimes[R] ℬ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary construction used to build the `Mul` instance and get distributivity o
f `+` and
`\smul`.
-/
noncomputable def mulHom : (𝒜 ᵍ⊗[R] ℬ) →ₗ[R] (𝒜 ᵍ⊗[R] ℬ) →ₗ[R] (𝒜 ᵍ⊗[R] ℬ) := by
  letI fAB1 := auxEquiv R 𝒜 ℬ
  have := ((gradedMul R (𝒜 ·) (ℬ ·)).compl₁₂ fAB1.toLinearMap fAB1.toLinearMap).compr₂
    fAB1.symm.toLinearMap
  exact this
/-
**GradedTensorProduct.mulHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `GradedTensorProduc
t`。
形式化陈述：mulHom_apply (x y : 𝒜 ᵍotimes[R] ℬ) : mulHom 𝒜 ℬ x y = (auxEquiv R 𝒜 ℬ).sy
mm (gradedMul R (𝒜 ·) (ℬ ·) (auxEquiv R 𝒜 ℬ x) (auxEquiv R 𝒜 ℬ y))
参数：x y : 𝒜 ᵍotimes[R] ℬ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulHom_apply (x y : 𝒜 ᵍ⊗[R] ℬ) :
    mulHom 𝒜 ℬ x y
      = (auxEquiv R 𝒜 ℬ).symm (gradedMul R (𝒜 ·) (ℬ ·) (auxEquiv R 𝒜 ℬ x) (auxEquiv R 𝒜 ℬ y)) :=
  rfl

/-- The multiplication on the graded tensor product.

See `GradedTensorProduct.coe_mul_coe` for a characterization on pure tensors. -/
/-
**GradedTensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `GradedTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplication on the graded tensor product.

See `GradedTensorProduct.coe_mul_coe` for a characterization on pure tensors.
-/
instance : Mul (𝒜 ᵍ⊗[R] ℬ) where mul x y := mulHom 𝒜 ℬ x y
/-
**GradedTensorProduct.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `GradedTensorProduct`。
形式化陈述：mul_def (x y : 𝒜 ᵍotimes[R] ℬ) : x * y = mulHom 𝒜 ℬ x y
参数：x y : 𝒜 ᵍotimes[R] ℬ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def (x y : 𝒜 ᵍ⊗[R] ℬ) : x * y = mulHom 𝒜 ℬ x y := rfl

-- Before https://github.com/leanprover-community/mathlib4/pull/8386 this was `@[simp]` but it times out when we try to apply it.
/-
**GradedTensorProduct.auxEquiv_mul** 是 Mathlib 中的一个定理，位于命名空间 `GradedTensorProduc
t`。
形式化陈述：auxEquiv_mul (x y : 𝒜 ᵍotimes[R] ℬ) : auxEquiv R 𝒜 ℬ (x * y) = gradedMul R
 (𝒜 ·) (ℬ ·) (auxEquiv R 𝒜 ℬ x) (auxEquiv R 𝒜 ℬ y)
参数：x y : 𝒜 ᵍotimes[R] ℬ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DirectSum.instSMulCommClass`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `LinearEquiv.eq_symm_apply`：eq_symm_apply {x y} : y = e.symm x ↔ e y = x
-/
theorem auxEquiv_mul (x y : 𝒜 ᵍ⊗[R] ℬ) :
    auxEquiv R 𝒜 ℬ (x * y) = gradedMul R (𝒜 ·) (ℬ ·) (auxEquiv R 𝒜 ℬ x) (auxEquiv R 𝒜 ℬ y) :=
  LinearEquiv.eq_symm_apply _ |>.mp rfl
/-
**GradedTensorProduct.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `GradedTensorProduct`
。
形式化陈述：instMonoid : Monoid (𝒜 ᵍotimes[R] ℬ) where mul_one x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoid : Monoid (𝒜 ᵍ⊗[R] ℬ) where
  mul_one x := by
    rw [mul_def, mulHom_apply, auxEquiv_one, gradedMul_one, LinearEquiv.symm_apply_apply]
  one_mul x := by
    rw [mul_def, mulHom_apply, auxEquiv_one, one_gradedMul, LinearEquiv.symm_apply_apply]
  mul_assoc x y z := by
    simp_rw [mul_def, mulHom_apply, LinearEquiv.apply_symm_apply]
    rw [gradedMul_assoc]
/-
**GradedTensorProduct.instRing** 是 Mathlib 中的一个实例，位于命名空间 `GradedTensorProduct`。
形式化陈述：instRing : Ring (𝒜 ᵍotimes[R] ℬ) where right_distrib x y z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRing : Ring (𝒜 ᵍ⊗[R] ℬ) where
  right_distrib x y z := by simp_rw [mul_def, LinearMap.map_add₂]
  left_distrib x y z := by simp_rw [mul_def, map_add]
  mul_zero x := by simp_rw [mul_def, map_zero]
  zero_mul x := by simp_rw [mul_def, LinearMap.map_zero₂]

/-- The characterization of this multiplication on partially homogeneous elements. -/
/-
**GradedTensorProduct.tmul_coe_mul_coe_tmul** 是 Mathlib 中的一个定理，位于命名空间 `GradedTen
sorProduct`。
形式化陈述：tmul_coe_mul_coe_tmul {j₁ i₂ : ι} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : B
) : (a₁ ᵍotimesₜ[R] (b₁ : B) * (a₂ : A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotimes[R] ℬ) = (-1 :
 Intˣ) ^ (j₁ * i₂) • ((a₁ * a₂ : A) ᵍotimesₜ (b₁ * b₂ : B))
参数：a₁ : A；b₁ : ℬ j₁；a₂ : 𝒜 i₂；b₂ : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.instSMulCommClass`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.decompose_coe`：decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (
x : M) = DirectSum.of _ i x
· 使用定理 `TensorProduct.tmul_of_gradedMul_of_tmul`：tmul_of_gradedMul_of_tmul (j₁ i
₂ : ι) (a₁ : ⨁ i, 𝒜 i) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : ⨁ i, ℬ i) : gradedMul R 𝒜 ℬ
 (a₁ otimesₜ lof R _ ℬ j₁ b₁)…
· 使用定理 `Units.smul_def`：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_
1 : SMul M α] (m : Mˣ) (a : α), m • a = ↑m • a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `LinearEquiv.map_smul`：map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e 
(c • x) = c • e x
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `TensorProduct.congr_symm_tmul`：congr_symm_tmul (f : M ≃ₛₗ[σ₁₂] M₂) (g : 
N ≃ₛₗ[σ₁₂] N₂) (p : M₂) (q : N₂) : (congr f g).symm (p otimesₜ q) = f.symm p oti
mesₜ g.symm q
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DirectSum.decompose_symm_mul`：decompose_symm_mul (x y : ⨁ i, 𝒜 i) : (dec
ompose 𝒜).symm (x * y) = (decompose 𝒜).symm x * (decompose 𝒜).symm y
· 使用定理 `DirectSum.decompose_symm_of`：decompose_symm_of {i : ι} (x : ℳ i) : (deco
mpose ℳ).symm (DirectSum.of _ i x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The characterization of this multiplication on partially homogeneous elements.
-/
theorem tmul_coe_mul_coe_tmul {j₁ i₂ : ι} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : B) :
    (a₁ ᵍ⊗ₜ[R] (b₁ : B) * (a₂ : A) ᵍ⊗ₜ[R] b₂ : 𝒜 ᵍ⊗[R] ℬ) =
      (-1 : ℤˣ) ^ (j₁ * i₂) • ((a₁ * a₂ : A) ᵍ⊗ₜ (b₁ * b₂ : B)) := by
  dsimp only [mul_def, mulHom_apply, of_symm_of]
  dsimp [auxEquiv, tmul]
  rw [decompose_coe, decompose_coe]
  simp_rw [← lof_eq_of R]
  rw [tmul_of_gradedMul_of_tmul]
  simp_rw [lof_eq_of R]
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_smul` to `LinearEquiv.map_smul`
  rw [@Units.smul_def _ _ (_) (_), ← Int.cast_smul_eq_zsmul R, LinearEquiv.map_smul, map_smul,
    Int.cast_smul_eq_zsmul R, ← @Units.smul_def _ _ (_) (_)]
  rw [congr_symm_tmul]
  dsimp
  simp_rw [decompose_symm_mul, decompose_symm_of, Equiv.symm_apply_apply]

/-- A special case for when `b₁` has grade 0. -/
/-
**GradedTensorProduct.tmul_zero_coe_mul_coe_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Grad
edTensorProduct`。
形式化陈述：tmul_zero_coe_mul_coe_tmul {i₂ : ι} (a₁ : A) (b₁ : ℬ 0) (a₂ : 𝒜 i₂) (b₂ : 
B) : (a₁ ᵍotimesₜ[R] (b₁ : B) * (a₂ : A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotimes[R] ℬ) = ((a₁
 * a₂ : A) ᵍotimesₜ (b₁ * b₂ : B))
参数：a₁ : A；b₁ : ℬ 0；a₂ : 𝒜 i₂；b₂ : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GradedTensorProduct.tmul_coe_mul_coe_tmul`：tmul_coe_mul_coe_tmul {j₁ i₂ 
: ι} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : B) : (a₁ ᵍotimesₜ[R] (b₁ : B) * (a₂ 
: A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotimes…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `uzpow_zero`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : _root_.Mo
dule R (Additive ℤˣ)] (s : ℤˣ), s ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
A special case for when `b₁` has grade 0.
-/
theorem tmul_zero_coe_mul_coe_tmul {i₂ : ι} (a₁ : A) (b₁ : ℬ 0) (a₂ : 𝒜 i₂) (b₂ : B) :
    (a₁ ᵍ⊗ₜ[R] (b₁ : B) * (a₂ : A) ᵍ⊗ₜ[R] b₂ : 𝒜 ᵍ⊗[R] ℬ) =
      ((a₁ * a₂ : A) ᵍ⊗ₜ (b₁ * b₂ : B)) := by
  rw [tmul_coe_mul_coe_tmul, zero_mul, uzpow_zero, one_smul]

/-- A special case for when `a₂` has grade 0. -/
/-
**GradedTensorProduct.tmul_coe_mul_zero_coe_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Grad
edTensorProduct`。
形式化陈述：tmul_coe_mul_zero_coe_tmul {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 0) (b₂ : 
B) : (a₁ ᵍotimesₜ[R] (b₁ : B) * (a₂ : A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotimes[R] ℬ) = ((a₁
 * a₂ : A) ᵍotimesₜ (b₁ * b₂ : B))
参数：a₁ : A；b₁ : ℬ j₁；a₂ : 𝒜 0；b₂ : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GradedTensorProduct.tmul_coe_mul_coe_tmul`：tmul_coe_mul_coe_tmul {j₁ i₂ 
: ι} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : B) : (a₁ ᵍotimesₜ[R] (b₁ : B) * (a₂ 
: A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotimes…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `uzpow_zero`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : _root_.Mo
dule R (Additive ℤˣ)] (s : ℤˣ), s ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
A special case for when `a₂` has grade 0.
-/
theorem tmul_coe_mul_zero_coe_tmul {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 0) (b₂ : B) :
    (a₁ ᵍ⊗ₜ[R] (b₁ : B) * (a₂ : A) ᵍ⊗ₜ[R] b₂ : 𝒜 ᵍ⊗[R] ℬ) =
      ((a₁ * a₂ : A) ᵍ⊗ₜ (b₁ * b₂ : B)) := by
  rw [tmul_coe_mul_coe_tmul, mul_zero, uzpow_zero, one_smul]
/-
**GradedTensorProduct.tmul_one_mul_coe_tmul** 是 Mathlib 中的一个定理，位于命名空间 `GradedTen
sorProduct`。
形式化陈述：tmul_one_mul_coe_tmul {i₂ : ι} (a₁ : A) (a₂ : 𝒜 i₂) (b₂ : B) : (a₁ ᵍotimes
ₜ[R] (1 : B) * (a₂ : A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotimes[R] ℬ) = (a₁ * a₂ : A) ᵍotimes
ₜ (b₂ : B)
参数：a₁ : A；a₂ : 𝒜 i₂；b₂ : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.coe_gOne`：SetLike.coe_gOne {S : Type*} [SetLike S R] [One R] [Ze
ro ι] (A : ι -> S) [SetLike.GradedOne A] : ↑(@GradedMonoid.GOne.one _ (fun i => 
A i) _…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `GradedTensorProduct.tmul_zero_coe_mul_coe_tmul`：tmul_zero_coe_mul_coe_tm
ul {i₂ : ι} (a₁ : A) (b₁ : ℬ 0) (a₂ : 𝒜 i₂) (b₂ : B) : (a₁ ᵍotimesₜ[R] (b₁ : B) 
* (a₂ : A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotime…
-/
theorem tmul_one_mul_coe_tmul {i₂ : ι} (a₁ : A) (a₂ : 𝒜 i₂) (b₂ : B) :
    (a₁ ᵍ⊗ₜ[R] (1 : B) * (a₂ : A) ᵍ⊗ₜ[R] b₂ : 𝒜 ᵍ⊗[R] ℬ) = (a₁ * a₂ : A) ᵍ⊗ₜ (b₂ : B) := by
  convert! tmul_zero_coe_mul_coe_tmul 𝒜 ℬ a₁ (@GradedMonoid.GOne.one _ (ℬ ·) _ _) a₂ b₂
  rw [SetLike.coe_gOne, one_mul]
/-
**GradedTensorProduct.tmul_coe_mul_one_tmul** 是 Mathlib 中的一个定理，位于命名空间 `GradedTen
sorProduct`。
形式化陈述：tmul_coe_mul_one_tmul {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (b₂ : B) : (a₁ ᵍotimes
ₜ[R] (b₁ : B) * (1 : A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotimes[R] ℬ) = (a₁ : A) ᵍotimesₜ (b₁
 * b₂ : B)
参数：a₁ : A；b₁ : ℬ j₁；b₂ : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.coe_gOne`：SetLike.coe_gOne {S : Type*} [SetLike S R] [One R] [Ze
ro ι] (A : ι -> S) [SetLike.GradedOne A] : ↑(@GradedMonoid.GOne.one _ (fun i => 
A i) _…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `GradedTensorProduct.tmul_coe_mul_zero_coe_tmul`：tmul_coe_mul_zero_coe_tm
ul {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 0) (b₂ : B) : (a₁ ᵍotimesₜ[R] (b₁ : B) 
* (a₂ : A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotime…
-/
theorem tmul_coe_mul_one_tmul {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (b₂ : B) :
    (a₁ ᵍ⊗ₜ[R] (b₁ : B) * (1 : A) ᵍ⊗ₜ[R] b₂ : 𝒜 ᵍ⊗[R] ℬ) = (a₁ : A) ᵍ⊗ₜ (b₁ * b₂ : B) := by
  convert! tmul_coe_mul_zero_coe_tmul 𝒜 ℬ a₁ b₁ (@GradedMonoid.GOne.one _ (𝒜 ·) _ _) b₂
  rw [SetLike.coe_gOne, mul_one]
/-
**GradedTensorProduct.tmul_one_mul_one_tmul** 是 Mathlib 中的一个定理，位于命名空间 `GradedTen
sorProduct`。
形式化陈述：tmul_one_mul_one_tmul (a₁ : A) (b₂ : B) : (a₁ ᵍotimesₜ[R] (1 : B) * (1 : A
) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotimes[R] ℬ) = (a₁ : A) ᵍotimesₜ (b₂ : B)
参数：a₁ : A；b₂ : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.coe_gOne`：SetLike.coe_gOne {S : Type*} [SetLike S R] [One R] [Ze
ro ι] (A : ι -> S) [SetLike.GradedOne A] : ↑(@GradedMonoid.GOne.one _ (fun i => 
A i) _…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `GradedTensorProduct.tmul_coe_mul_zero_coe_tmul`：tmul_coe_mul_zero_coe_tm
ul {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 0) (b₂ : B) : (a₁ ᵍotimesₜ[R] (b₁ : B) 
* (a₂ : A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotime…
-/
theorem tmul_one_mul_one_tmul (a₁ : A) (b₂ : B) :
    (a₁ ᵍ⊗ₜ[R] (1 : B) * (1 : A) ᵍ⊗ₜ[R] b₂ : 𝒜 ᵍ⊗[R] ℬ) = (a₁ : A) ᵍ⊗ₜ (b₂ : B) := by
  convert!
    tmul_coe_mul_zero_coe_tmul 𝒜 ℬ a₁ (GradedMonoid.GOne.one (A := (ℬ ·)))
      (GradedMonoid.GOne.one (A := (𝒜 ·))) b₂
  · rw [SetLike.coe_gOne, mul_one]
  · rw [SetLike.coe_gOne, one_mul]

/-- The ring morphism `A →+* A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
@[simps]
/-
**GradedTensorProduct.includeLeftRingHom** 是 Mathlib 中的一个定义，位于命名空间 `GradedTensor
Product`。
形式化陈述：includeLeftRingHom : A ->+* 𝒜 ᵍotimes[R] ℬ where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring morphism `A →+* A ⊗[R] B` sending `a` to `a ⊗ₜ 1`.
-/
def includeLeftRingHom : A →+* 𝒜 ᵍ⊗[R] ℬ where
  toFun a := a ᵍ⊗ₜ 1
  map_zero' := by simp
  map_add' := by simp [tmul, TensorProduct.add_tmul]
  map_one' := rfl
  map_mul' a₁ a₂ := by
    classical
    rw [← DirectSum.sum_support_decompose 𝒜 a₂, Finset.mul_sum]
    simp_rw [tmul, sum_tmul, map_sum, Finset.mul_sum]
    congr
    ext i
    rw [← SetLike.coe_gOne ℬ, tmul_coe_mul_coe_tmul, zero_mul, uzpow_zero, one_smul,
      SetLike.coe_gOne, one_mul]

set_option backward.defeqAttrib.useBackward true in
/-
**GradedTensorProduct.instAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `GradedTensorProduct
`。
形式化陈述：instAlgebra : Algebra R (𝒜 ᵍotimes[R] ℬ) where algebraMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAlgebra : Algebra R (𝒜 ᵍ⊗[R] ℬ) where
  algebraMap := (includeLeftRingHom 𝒜 ℬ).comp (algebraMap R A)
  commutes' r x := by
    dsimp [mul_def, mulHom_apply, auxEquiv_tmul]
    simp_rw [DirectSum.decompose_algebraMap, DirectSum.decompose_one, algebraMap_gradedMul,
      gradedMul_algebraMap]
  smul_def' r x := by
    dsimp [mul_def, mulHom_apply, auxEquiv_tmul]
    simp_rw [DirectSum.decompose_algebraMap, DirectSum.decompose_one, algebraMap_gradedMul]
    -- Qualified `map_smul` to avoid a TC timeout https://github.com/leanprover-community/mathlib4/pull/8386
    rw [LinearEquiv.map_smul]
    simp
/-
**GradedTensorProduct.algebraMap_def** 是 Mathlib 中的一个引理，位于命名空间 `GradedTensorProd
uct`。
形式化陈述：algebraMap_def (r : R) : algebraMap R (𝒜 ᵍotimes[R] ℬ) r = algebraMap R A 
r ᵍotimesₜ[R] 1
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma algebraMap_def (r : R) : algebraMap R (𝒜 ᵍ⊗[R] ℬ) r = algebraMap R A r ᵍ⊗ₜ[R] 1 := rfl
/-
**GradedTensorProduct.tmul_algebraMap_mul_coe_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Gr
adedTensorProduct`。
形式化陈述：tmul_algebraMap_mul_coe_tmul {i₂ : ι} (a₁ : A) (r : R) (a₂ : 𝒜 i₂) (b₂ : B
) : (a₁ ᵍotimesₜ[R] algebraMap R B r * (a₂ : A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotimes[R] ℬ)
 = (a₁ * a₂ : A) ᵍotimesₜ (algebraMap R B r * b₂ : B)
参数：a₁ : A；r : R；a₂ : 𝒜 i₂；b₂ : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedTensorProduct.tmul_zero_coe_mul_coe_tmul`：tmul_zero_coe_mul_coe_tm
ul {i₂ : ι} (a₁ : A) (b₁ : ℬ 0) (a₂ : 𝒜 i₂) (b₂ : B) : (a₁ ᵍotimesₜ[R] (b₁ : B) 
* (a₂ : A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotime…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
-/
theorem tmul_algebraMap_mul_coe_tmul {i₂ : ι} (a₁ : A) (r : R) (a₂ : 𝒜 i₂) (b₂ : B) :
    (a₁ ᵍ⊗ₜ[R] algebraMap R B r * (a₂ : A) ᵍ⊗ₜ[R] b₂ : 𝒜 ᵍ⊗[R] ℬ)
      = (a₁ * a₂ : A) ᵍ⊗ₜ (algebraMap R B r * b₂ : B) :=
  tmul_zero_coe_mul_coe_tmul 𝒜 ℬ a₁ (GAlgebra.toFun (A := (ℬ ·)) r) a₂ b₂
/-
**GradedTensorProduct.tmul_coe_mul_algebraMap_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Gr
adedTensorProduct`。
形式化陈述：tmul_coe_mul_algebraMap_tmul {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (r : R) (b₂ : B
) : (a₁ ᵍotimesₜ[R] (b₁ : B) * algebraMap R A r ᵍotimesₜ[R] b₂ : 𝒜 ᵍotimes[R] ℬ)
 = (a₁ * algebraMap R A r : A) ᵍotimesₜ (b₁ * b₂ : B)
参数：a₁ : A；b₁ : ℬ j₁；r : R；b₂ : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedTensorProduct.tmul_coe_mul_zero_coe_tmul`：tmul_coe_mul_zero_coe_tm
ul {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 0) (b₂ : B) : (a₁ ᵍotimesₜ[R] (b₁ : B) 
* (a₂ : A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotime…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
-/
theorem tmul_coe_mul_algebraMap_tmul {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (r : R) (b₂ : B) :
    (a₁ ᵍ⊗ₜ[R] (b₁ : B) * algebraMap R A r ᵍ⊗ₜ[R] b₂ : 𝒜 ᵍ⊗[R] ℬ)
      = (a₁ * algebraMap R A r : A) ᵍ⊗ₜ (b₁ * b₂ : B) :=
  tmul_coe_mul_zero_coe_tmul 𝒜 ℬ a₁ b₁ (GAlgebra.toFun (A := (𝒜 ·)) r) b₂

/-- The algebra morphism `A →ₐ[R] A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
@[simps!]
/-
**GradedTensorProduct.includeLeft** 是 Mathlib 中的一个定义，位于命名空间 `GradedTensorProduct
`。
形式化陈述：includeLeft : A ->ₐ[R] 𝒜 ᵍotimes[R] ℬ where toRingHom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra morphism `A →ₐ[R] A ⊗[R] B` sending `a` to `a ⊗ₜ 1`.
-/
def includeLeft : A →ₐ[R] 𝒜 ᵍ⊗[R] ℬ where
  toRingHom := includeLeftRingHom 𝒜 ℬ
  commutes' _ := rfl

/-- The algebra morphism `B →ₐ[R] A ⊗[R] B` sending `b` to `1 ⊗ₜ b`. -/
@[simps!]
/-
**GradedTensorProduct.includeRight** 是 Mathlib 中的一个定义，位于命名空间 `GradedTensorProduc
t`。
形式化陈述：includeRight : B ->ₐ[R] (𝒜 ᵍotimes[R] ℬ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra morphism `B →ₐ[R] A ⊗[R] B` sending `b` to `1 ⊗ₜ b`.
-/
def includeRight : B →ₐ[R] (𝒜 ᵍ⊗[R] ℬ) :=
  AlgHom.ofLinearMap (R := R) (A := B) (B := 𝒜 ᵍ⊗[R] ℬ)
    (f := {
       toFun := fun b => 1 ᵍ⊗ₜ b
       map_add' := by simp [tmul, TensorProduct.tmul_add]
       map_smul' := by simp [tmul, TensorProduct.tmul_smul] })
    (map_one := rfl)
    (map_mul := by
      rw [LinearMap.map_mul_iff]
      refine DirectSum.decompose_lhom_ext ℬ fun i₁ => ?_
      ext b₁ b₂ : 2
      dsimp
      rw [tmul_coe_mul_one_tmul])
/-
**GradedTensorProduct.algebraMap_def'** 是 Mathlib 中的一个引理，位于命名空间 `GradedTensorPro
duct`。
形式化陈述：algebraMap_def' (r : R) : algebraMap R (𝒜 ᵍotimes[R] ℬ) r = 1 ᵍotimesₜ[R] 
algebraMap R B r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
-/
lemma algebraMap_def' (r : R) : algebraMap R (𝒜 ᵍ⊗[R] ℬ) r = 1 ᵍ⊗ₜ[R] algebraMap R B r :=
  (includeRight 𝒜 ℬ).commutes r |>.symm

variable {C} [Ring C] [Algebra R C]

set_option backward.defeqAttrib.useBackward true in
/-- The forwards direction of the universal property; an algebra morphism out of the graded tensor
product can be assembled from maps on each component that (anti)commute on pure elements of the
corresponding graded algebras. -/
/-
**GradedTensorProduct.lift** 是 Mathlib 中的一个定义，位于命名空间 `GradedTensorProduct`。
形式化陈述：lift (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) (h_anti_commutes : forall ⦃i j⦄ (a 
: 𝒜 i) (b : ℬ j), f a * g b = (-1 : Intˣ) ^ (j * i) • (g b * f a)) : (𝒜 ᵍotimes[
R] ℬ) ->ₐ[R] C
参数：f : A ->ₐ[R] C；g : B ->ₐ[R] C；h_anti_commutes : forall ⦃i j⦄ (a : 𝒜 i) (b : ℬ
 j), f a * g b = (-1 : Intˣ) ^ (j * i) • (g b * f a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forwards direction of the universal property; an algebra morphism out of the
 graded tensor
product can be assembled from maps on each component that (anti)commute on pure 
elements of the
corresponding graded algebras.
-/
def lift (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h_anti_commutes : ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j), f a * g b = (-1 : ℤˣ) ^ (j * i) • (g b * f a)) :
    (𝒜 ᵍ⊗[R] ℬ) →ₐ[R] C :=
  AlgHom.ofLinearMap
    (LinearMap.mul' R C
      ∘ₗ (TensorProduct.map f.toLinearMap g.toLinearMap)
      ∘ₗ ((of R 𝒜 ℬ).symm : 𝒜 ᵍ⊗[R] ℬ →ₗ[R] A ⊗[R] B))
    (by
      dsimp [Algebra.TensorProduct.one_def]
      simp only [map_one, mul_one])
    (by
      rw [LinearMap.map_mul_iff]
      ext a₁ : 3
      refine DirectSum.decompose_lhom_ext ℬ fun j₁ => ?_
      ext b₁ : 3
      refine DirectSum.decompose_lhom_ext 𝒜 fun i₂ => ?_
      ext a₂ b₂ : 2
      dsimp
      rw [tmul_coe_mul_coe_tmul]
      rw [@Units.smul_def _ _ (_) (_), ← Int.cast_smul_eq_zsmul R, map_smul, map_smul, map_smul]
      rw [Int.cast_smul_eq_zsmul R, ← @Units.smul_def _ _ (_) (_)]
      rw [of_symm_of, map_tmul, LinearMap.mul'_apply]
      simp_rw [AlgHom.toLinearMap_apply, map_mul]
      simp_rw [mul_assoc (f a₁), ← mul_assoc _ _ (g b₂), h_anti_commutes, mul_smul_comm,
        smul_mul_assoc, smul_smul, Int.units_mul_self, one_smul])

@[simp]
/-
**GradedTensorProduct.lift_tmul** 是 Mathlib 中的一个定理，位于命名空间 `GradedTensorProduct`。
形式化陈述：lift_tmul (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) (h_anti_commutes : forall ⦃i j
⦄ (a : 𝒜 i) (b : ℬ j), f a * g b = (-1 : Intˣ) ^ (j * i) • (g b * f a)) (a : A) 
(b : B) : lift 𝒜 ℬ f g h_anti_commutes (a ᵍotimesₜ b) = f a * g b
参数：f : A ->ₐ[R] C；g : B ->ₐ[R] C；h_anti_commutes : forall ⦃i j⦄ (a : 𝒜 i) (b : ℬ
 j), f a * g b = (-1 : Intˣ) ^ (j * i) • (g b * f a)；a : A；b : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_tmul (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h_anti_commutes : ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j), f a * g b = (-1 : ℤˣ) ^ (j * i) • (g b * f a))
    (a : A) (b : B) :
    lift 𝒜 ℬ f g h_anti_commutes (a ᵍ⊗ₜ b) = f a * g b :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- The universal property of the graded tensor product; every algebra morphism uniquely factors
as a pair of algebra morphisms that anticommute with respect to the grading. -/
/-
**GradedTensorProduct.liftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `GradedTensorProduct`。
形式化陈述：liftEquiv : { fg : (A ->ₐ[R] C) × (B ->ₐ[R] C) // forall ⦃i j⦄ (a : 𝒜 i) (
b : ℬ j), fg.1 a * fg.2 b = (-1 : Intˣ)^(j * i) • (fg.2 b * fg.1 a)} ≃ ((𝒜 ᵍotim
es[R] ℬ) ->ₐ[R] C) where toFun fg
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of the graded tensor product; every algebra morphism uniq
uely factors
as a pair of algebra morphisms that anticommute with respect to the grading.
-/
def liftEquiv :
    { fg : (A →ₐ[R] C) × (B →ₐ[R] C) //
        ∀ ⦃i j⦄ (a : 𝒜 i) (b : ℬ j), fg.1 a * fg.2 b = (-1 : ℤˣ)^(j * i) • (fg.2 b * fg.1 a)} ≃
      ((𝒜 ᵍ⊗[R] ℬ) →ₐ[R] C) where
  toFun fg := lift 𝒜 ℬ _ _ fg.prop
  invFun F := ⟨(F.comp (includeLeft 𝒜 ℬ), F.comp (includeRight 𝒜 ℬ)), fun i j a b => by
    dsimp
    rw [← map_mul, ← map_mul F, tmul_coe_mul_coe_tmul, one_mul, mul_one, AlgHom.map_smul_of_tower,
      tmul_one_mul_one_tmul, smul_smul, Int.units_mul_self, one_smul]⟩
  left_inv fg := by ext <;> (dsimp; simp only [map_one, mul_one, one_mul])
  right_inv F := by
    apply AlgHom.toLinearMap_injective
    ext
    dsimp
    rw [← map_mul, tmul_one_mul_one_tmul]

/-- Two algebra morphism from the graded tensor product agree if their compositions with the left
and right inclusions agree. -/
@[ext]
/-
**GradedTensorProduct.algHom_ext** 是 Mathlib 中的一个引理，位于命名空间 `GradedTensorProduct`
。
形式化陈述：algHom_ext ⦃f g : (𝒜 ᵍotimes[R] ℬ) ->ₐ[R] C⦄ (ha : f.comp (includeLeft 𝒜 ℬ
) = g.comp (includeLeft 𝒜 ℬ)) (hb : f.comp (includeRight 𝒜 ℬ) = g.comp (includeR
ight 𝒜 ℬ)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y

--- 原说明 ---
Two algebra morphism from the graded tensor product agree if their compositions 
with the left
and right inclusions agree.
-/
lemma algHom_ext ⦃f g : (𝒜 ᵍ⊗[R] ℬ) →ₐ[R] C⦄
    (ha : f.comp (includeLeft 𝒜 ℬ) = g.comp (includeLeft 𝒜 ℬ))
    (hb : f.comp (includeRight 𝒜 ℬ) = g.comp (includeRight 𝒜 ℬ)) : f = g :=
  (liftEquiv 𝒜 ℬ).symm.injective <| Subtype.ext <| Prod.ext ha hb

/-- The non-trivial symmetric braiding, sending $a \otimes b$ to
$(-1)^{\deg a' \deg b} (b \otimes a)$. -/
/-
**GradedTensorProduct.comm** 是 Mathlib 中的一个定义，位于命名空间 `GradedTensorProduct`。
形式化陈述：comm : (𝒜 ᵍotimes[R] ℬ) ≃ₐ[R] (ℬ ᵍotimes[R] 𝒜)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The non-trivial symmetric braiding, sending $a \otimes b$ to
$(-1)^{\deg a' \deg b} (b \otimes a)$.
-/
def comm : (𝒜 ᵍ⊗[R] ℬ) ≃ₐ[R] (ℬ ᵍ⊗[R] 𝒜) :=
  AlgEquiv.ofLinearEquiv
    (auxEquiv R 𝒜 ℬ ≪≫ₗ gradedComm R _ _ ≪≫ₗ (auxEquiv R ℬ 𝒜).symm)
    (by
      dsimp
      simp_rw [auxEquiv_one, gradedComm_one, auxEquiv_symm_one])
    (fun x y => by
      dsimp
      simp_rw [auxEquiv_mul, gradedComm_gradedMul, LinearEquiv.symm_apply_eq,
        ← gradedComm_gradedMul, auxEquiv_mul, LinearEquiv.apply_symm_apply, gradedComm_gradedMul])
/-
**GradedTensorProduct.auxEquiv_comm** 是 Mathlib 中的一个引理，位于命名空间 `GradedTensorProdu
ct`。
形式化陈述：auxEquiv_comm (x : 𝒜 ᵍotimes[R] ℬ) : auxEquiv R ℬ 𝒜 (comm 𝒜 ℬ x) = gradedC
omm R (𝒜 ·) (ℬ ·) (auxEquiv R 𝒜 ℬ x)
参数：x : 𝒜 ᵍotimes[R] ℬ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearEquiv.eq_symm_apply`：eq_symm_apply {x y} : y = e.symm x ↔ e y = x
-/
lemma auxEquiv_comm (x : 𝒜 ᵍ⊗[R] ℬ) :
    auxEquiv R ℬ 𝒜 (comm 𝒜 ℬ x) = gradedComm R (𝒜 ·) (ℬ ·) (auxEquiv R 𝒜 ℬ x) :=
  LinearEquiv.eq_symm_apply _ |>.mp rfl
/-
**GradedTensorProduct.comm_coe_tmul_coe** 是 Mathlib 中的一个定理，位于命名空间 `GradedTensorP
roduct`。
形式化陈述：∀ {R : Type u_1} {ι : Type u_2} {A : Type u_3} {B : Type u_4} [inst : Comm
Semiring ι] [inst_1 : DecidableEq ι]   [inst_2 : CommRing R] [inst_3 : Ring A] [
inst_4 : Ring B] [inst_5 : Algebra R A] [inst_6 : Algebra R B]   (𝒜 : ι → Submod
ule R A) (ℬ : ι → Submodule R B) [inst_7 : GradedAlgebra 𝒜] [inst_8 : GradedAlge
bra ℬ]   [inst_9 : _root_.Module ι (Additive ℤˣ)] {i j : ι} (a : ↥(𝒜 i)) (b : ↥(
ℬ j)),   (GradedTensorProduct.comm 𝒜 ℬ) (↑a ᵍ⊗ₜ[R] ↑b) = (-1) ^ (j * i) • ↑b ᵍ⊗ₜ
[R] ↑a
参数：𝒜 : ι → Submodule R A；ℬ : ι → Submodule R B；Additive ℤˣ；a : ↥(𝒜 i)；b : ↥(ℬ j)
；GradedTensorProduct.comm 𝒜 ℬ；↑a ᵍ⊗ₜ[R] ↑b；-1；j * i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `GradedTensorProduct.auxEquiv_comm`：auxEquiv_comm (x : 𝒜 ᵍotimes[R] ℬ) : 
auxEquiv R ℬ 𝒜 (comm 𝒜 ℬ x) = gradedComm R (𝒜 ·) (ℬ ·) (auxEquiv R 𝒜 ℬ x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DirectSum.decompose_coe`：decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (
x : M) = DirectSum.of _ i x
· 使用定理 `TensorProduct.gradedComm_of_tmul_of`：gradedComm_of_tmul_of (i j : ι) (a 
: 𝒜 i) (b : ℬ j) : gradedComm R 𝒜 ℬ (lof R _ 𝒜 i a otimesₜ lof R _ ℬ j b) = (-1 
: Intˣ) ^ (j * i) • (lof …
· 使用定理 `Units.smul_def`：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_
1 : SMul M α] (m : Mˣ) (a : α), m • a = ↑m • a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `LinearEquiv.map_smul`：map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e 
(c • x) = c • e x
· 使用定理 `GradedTensorProduct.auxEquiv_tmul`：auxEquiv_tmul (a : A) (b : B) : auxEq
uiv R 𝒜 ℬ (a ᵍotimesₜ b) = decompose 𝒜 a otimesₜ decompose ℬ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma comm_coe_tmul_coe {i j : ι} (a : 𝒜 i) (b : ℬ j) :
    comm 𝒜 ℬ (a ᵍ⊗ₜ b) = (-1 : ℤˣ) ^ (j * i) • (b ᵍ⊗ₜ a : ℬ ᵍ⊗[R] 𝒜) :=
  (auxEquiv R ℬ 𝒜).injective <| by
    simp_rw [auxEquiv_comm, auxEquiv_tmul, decompose_coe, ← lof_eq_of R, gradedComm_of_tmul_of,
      @Units.smul_def _ _ (_) (_), ← Int.cast_smul_eq_zsmul R]
    -- Qualified `map_smul` to avoid a TC timeout https://github.com/leanprover-community/mathlib4/pull/8386
    rw [LinearEquiv.map_smul, auxEquiv_tmul]
    simp_rw [decompose_coe, lof_eq_of]

end GradedTensorProduct

