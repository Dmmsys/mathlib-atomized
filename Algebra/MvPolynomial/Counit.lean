/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval

/-!
## Counit morphisms for multivariate polynomials

One may consider the ring of multivariate polynomials `MvPolynomial A R` with coefficients in `R`
and variables indexed by `A`. If `A` is not just a type, but an algebra over `R`,
then there is a natural surjective algebra homomorphism `MvPolynomial A R →ₐ[R] A`
obtained by `X a ↦ a`.

### Main declarations

* `MvPolynomial.ACounit R A` is the natural surjective algebra homomorphism
  `MvPolynomial A R →ₐ[R] A` obtained by `X a ↦ a`
* `MvPolynomial.counit` is an “absolute” variant with `R = ℤ`
* `MvPolynomial.counitNat` is an “absolute” variant with `R = ℕ`

-/

@[expose] public section


namespace MvPolynomial

open Function

variable (A B R : Type*) [CommSemiring A] [CommSemiring B] [CommRing R] [Algebra A B]

/-- `MvPolynomial.ACounit A B` is the natural surjective algebra homomorphism
`MvPolynomial B A →ₐ[A] B` obtained by `X a ↦ a`.

See `MvPolynomial.counit` for the “absolute” variant with `A = ℤ`,
and `MvPolynomial.counitNat` for the “absolute” variant with `A = ℕ`. -/
/-
**MvPolynomial.ACounit** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：ACounit : MvPolynomial B A ->ₐ[A] B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MvPolynomial.ACounit A B` is the natural surjective algebra homomorphism
`MvPolynomial B A →ₐ[A] B` obtained by `X a ↦ a`.

See `MvPolynomial.counit` for the “absolute” variant with `A = ℤ`,
and `MvPolynomial.counitNat` for the “absolute” variant with `A = ℕ`.
-/
noncomputable def ACounit : MvPolynomial B A →ₐ[A] B :=
  aeval id

variable {B}

@[simp]
/-
**MvPolynomial.ACounit_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：ACounit_X (b : B) : ACounit A B (X b) = b
参数：b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
-/
theorem ACounit_X (b : B) : ACounit A B (X b) = b :=
  aeval_X _ b

variable {A} (B)
/-
**MvPolynomial.ACounit_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：ACounit_C (a : A) : ACounit A B (C a) = algebraMap A B a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.aeval_C`：aeval_C (r : R) : aeval f (C r) = algebraMap R S₁ 
r
-/
theorem ACounit_C (a : A) : ACounit A B (C a) = algebraMap A B a :=
  aeval_C _ a

variable (A)
/-
**MvPolynomial.ACounit_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：ACounit_surjective : Surjective (ACounit A B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ACounit_X`：ACounit_X (b : B) : ACounit A B (X b) = b
-/
theorem ACounit_surjective : Surjective (ACounit A B) := fun b => ⟨X b, ACounit_X A b⟩

/-- `MvPolynomial.counit R` is the natural surjective ring homomorphism
`MvPolynomial R ℤ →+* R` obtained by `X r ↦ r`.

See `MvPolynomial.ACounit` for a “relative” variant for algebras over a base ring,
and `MvPolynomial.counitNat` for the “absolute” variant with `R = ℕ`. -/
/-
**MvPolynomial.counit** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：counit : MvPolynomial R Int ->+* R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MvPolynomial.counit R` is the natural surjective ring homomorphism
`MvPolynomial R ℤ →+* R` obtained by `X r ↦ r`.

See `MvPolynomial.ACounit` for a “relative” variant for algebras over a base rin
g,
and `MvPolynomial.counitNat` for the “absolute” variant with `R = ℕ`.
-/
noncomputable def counit : MvPolynomial R ℤ →+* R :=
  (ACounit ℤ R).toRingHom

/-- `MvPolynomial.counitNat A` is the natural surjective ring homomorphism
`MvPolynomial A ℕ →+* A` obtained by `X a ↦ a`.

See `MvPolynomial.ACounit` for a “relative” variant for algebras over a base ring
and `MvPolynomial.counit` for the “absolute” variant with `A = ℤ`. -/
/-
**MvPolynomial.counitNat** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：counitNat : MvPolynomial A Nat ->+* A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MvPolynomial.counitNat A` is the natural surjective ring homomorphism
`MvPolynomial A ℕ →+* A` obtained by `X a ↦ a`.

See `MvPolynomial.ACounit` for a “relative” variant for algebras over a base rin
g
and `MvPolynomial.counit` for the “absolute” variant with `A = ℤ`.
-/
noncomputable def counitNat : MvPolynomial A ℕ →+* A :=
  ACounit ℕ A
/-
**MvPolynomial.counit_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：counit_surjective : Surjective (counit R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ACounit_surjective`：ACounit_surjective : Surjective (ACouni
t A B)
-/
theorem counit_surjective : Surjective (counit R) :=
  ACounit_surjective ℤ R
/-
**MvPolynomial.counitNat_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：counitNat_surjective : Surjective (counitNat A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ACounit_surjective`：ACounit_surjective : Surjective (ACouni
t A B)
-/
theorem counitNat_surjective : Surjective (counitNat A) :=
  ACounit_surjective ℕ A
/-
**MvPolynomial.counit_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：counit_C (n : Int) : counit R (C n) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ACounit_C`：ACounit_C (a : A) : ACounit A B (C a) = algebraM
ap A B a
-/
theorem counit_C (n : ℤ) : counit R (C n) = n :=
  ACounit_C _ _
/-
**MvPolynomial.counitNat_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：counitNat_C (n : Nat) : counitNat A (C n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ACounit_C`：ACounit_C (a : A) : ACounit A B (C a) = algebraM
ap A B a
-/
theorem counitNat_C (n : ℕ) : counitNat A (C n) = n :=
  ACounit_C _ _

variable {R A}

@[simp]
/-
**MvPolynomial.counit_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：counit_X (r : R) : counit R (X r) = r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ACounit_X`：ACounit_X (b : B) : ACounit A B (X b) = b
-/
theorem counit_X (r : R) : counit R (X r) = r :=
  ACounit_X _ _

@[simp]
/-
**MvPolynomial.counitNat_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：counitNat_X (a : A) : counitNat A (X a) = a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ACounit_X`：ACounit_X (b : B) : ACounit A B (X b) = b
-/
theorem counitNat_X (a : A) : counitNat A (X a) = a :=
  ACounit_X _ _

end MvPolynomial

