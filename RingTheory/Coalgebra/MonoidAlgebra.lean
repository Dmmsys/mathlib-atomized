/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# The coalgebra structure on monoid algebras

Given a type `X`, a commutative semiring `R` and a semiring `A` which is also an `R`-coalgebra,
this file collects results about the `R`-coalgebra instance on `A[X]` inherited from the
corresponding structure on its coefficients, defined in `Mathlib/RingTheory/Coalgebra/Basic.lean`.

## Main definitions

* `(Add)MonoidAlgebra.instCoalgebra`: the `R`-coalgebra structure on `A[X]` when `A` is an
  `R`-coalgebra.
* `LaurentPolynomial.instCoalgebra`: the `R`-coalgebra structure on the Laurent polynomials
  `A[T;T⁻¹]` when `A` is an `R`-coalgebra.
-/

public section

noncomputable section

open Coalgebra

namespace MonoidAlgebra

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A]
  {X : Type*} [Module R A] [Coalgebra R A]

variable (R A X) in
@[to_additive]
/-
**MonoidAlgebra.instCoalgebra** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
形式化陈述：instCoalgebra : Coalgebra R A[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoalgebra : Coalgebra R A[X] := coeffEquiv.coalgebra _

@[to_additive]
/-
**MonoidAlgebra.instIsCocomm** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
形式化陈述：instIsCocomm [IsCocomm R A] : IsCocomm R A[X]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.coalgebraIsCocomm`：coalgebraIsCocomm [AddCommMonoid B] [Module R B
] [Coalgebra R B] [IsCocomm R B] (e : A ≃ B) : letI
-/
instance instIsCocomm [IsCocomm R A] : IsCocomm R A[X] := coeffEquiv.coalgebraIsCocomm _

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.counit_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：counit_single (x : X) (a : A) : Coalgebra.counit (single x a) = Coalgebra.
counit (R
参数：x : X；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.counit_single`：counit_single (i : ι) (a : A) : counit (Finsupp.s
ingle i a) = counit (R
-/
lemma counit_single (x : X) (a : A) :
    Coalgebra.counit (single x a) = Coalgebra.counit (R := R) a :=
  Finsupp.counit_single _ _ _ _ _

@[to_additive]
/-
**MonoidAlgebra.comul_def** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：comul_def : Coalgebra.comul (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comul_def :
    Coalgebra.comul (R := R) (A := A[X]) =
      TensorProduct.map (coeffLinearEquiv R).symm.toLinearMap (coeffLinearEquiv R).symm.toLinearMap
        ∘ₗ comul ∘ₗ (coeffLinearEquiv R).toLinearMap := rfl

@[to_additive (dont_translate := R) (attr := simp)]
/-
**MonoidAlgebra.comul_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：comul_single (x : X) (a : A) : Coalgebra.comul (R
参数：x : X；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `Finsupp.comul_single`：comul_single (i : ι) (a : A) : comul (R
· 使用定理 `TensorProduct.map_map`：map_map (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂₃]
 N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) (x : M otimes[R] N) : map f₂ g₂
 (map f₁ g₁…
-/
lemma comul_single (x : X) (a : A) :
    Coalgebra.comul (R := R) (single x a) =
      TensorProduct.map (lsingle x) (lsingle x) (Coalgebra.comul a) := by
  simp [comul_def, TensorProduct.map_map]; rfl

end MonoidAlgebra

namespace LaurentPolynomial

open AddMonoidAlgebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Module R A] [Coalgebra R A]

/-
**LaurentPolynomial.instCoalgebra** 是 Mathlib 中的一个实例，位于命名空间 `LaurentPolynomial`。
形式化陈述：instCoalgebra : Coalgebra R A[T;T⁻¹]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoalgebra : Coalgebra R A[T;T⁻¹] := inferInstanceAs <| Coalgebra R A[ℤ]
/-
**LaurentPolynomial.instIsCocomm** 是 Mathlib 中的一个实例，位于命名空间 `LaurentPolynomial`。
形式化陈述：instIsCocomm [IsCocomm R A] : IsCocomm R A[T;T⁻¹]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsCocomm [IsCocomm R A] : IsCocomm R A[T;T⁻¹] := inferInstanceAs <| IsCocomm R A[ℤ]

variable {R A}

@[simp]
/-
**LaurentPolynomial.comul_C** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：comul_C (a : A) : Coalgebra.comul (R
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.comul_single`：∀ {R : Type u_1} [inst : CommSemiring R] 
{A : Type u_2} [inst_1 : Semiring A] {X : Type u_3}   [inst_2 : _root_.Module R 
A] [inst_3 : Coalge…
-/
theorem comul_C (a : A) :
    Coalgebra.comul (R := R) (C a) =
      TensorProduct.map (lsingle 0) (lsingle 0) (Coalgebra.comul (R := R) a) :=
  comul_single _ _

@[simp]
/-
**LaurentPolynomial.comul_C_mul_T** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：comul_C_mul_T (a : A) (n : Int) : Coalgebra.comul (R
参数：a : A；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.comul_single`：∀ {R : Type u_1} [inst : CommSemiring R] 
{A : Type u_2} [inst_1 : Semiring A] {X : Type u_3}   [inst_2 : _root_.Module R 
A] [inst_3 : Coalge…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comul_C_mul_T (a : A) (n : ℤ) :
    Coalgebra.comul (R := R) (C a * T n) =
      TensorProduct.map (lsingle n) (lsingle n) (Coalgebra.comul (R := R) a) := by
  simp [← single_eq_C_mul_T]
/-
**LaurentPolynomial.comul_C_mul_T_self** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynom
ial`。
形式化陈述：comul_C_mul_T_self (a : R) (n : Int) : Coalgebra.comul (C a * T n) = T n o
timesₜ[R] (C a * T n)
参数：a : R；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LaurentPolynomial.comul_C_mul_T`：comul_C_mul_T (a : A) (n : Int) : Coalg
ebra.comul (R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LaurentPolynomial.single_eq_C_mul_T`：single_eq_C_mul_T (r : R) (n : Int)
 : .single n r = C r * T n
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
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comul_C_mul_T_self (a : R) (n : ℤ) :
    Coalgebra.comul (C a * T n) = T n ⊗ₜ[R] (C a * T n) := by
  simp

@[simp]
/-
**LaurentPolynomial.counit_C** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：counit_C (a : A) : Coalgebra.counit (R
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.counit_single`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] {X : Type u_3}   [inst_2 : _root_.Module R
 A] [inst_3 : Coalge…
-/
theorem counit_C (a : A) :
    Coalgebra.counit (R := R) (C a) = Coalgebra.counit (R := R) a :=
  counit_single _ _

@[simp]
/-
**LaurentPolynomial.counit_C_mul_T** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`
。
形式化陈述：counit_C_mul_T (a : A) (n : Int) : Coalgebra.counit (R
参数：a : A；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.counit_single`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] {X : Type u_3}   [inst_2 : _root_.Module R
 A] [inst_3 : Coalge…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem counit_C_mul_T (a : A) (n : ℤ) :
    Coalgebra.counit (R := R) (C a * T n) = Coalgebra.counit (R := R) a := by
  simp [← single_eq_C_mul_T]

end LaurentPolynomial

