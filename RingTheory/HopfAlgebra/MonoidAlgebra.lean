/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The Hopf algebra structure on group algebras

Given a group `G`, a commutative semiring `R` and an `R`-Hopf algebra `A`, this file collects
results about the `R`-Hopf algebra instance on `A[G]`, building upon results in
`Mathlib/RingTheory/Bialgebra/MonoidAlgebra.lean` about the bialgebra structure.

## Main definitions

* `(Add)MonoidAlgebra.instHopfAlgebra`: the `R`-Hopf algebra structure on `A[G]` when `G` is an
  (add) group and `A` is an `R`-Hopf algebra.
* `LaurentPolynomial.instHopfAlgebra`: the `R`-Hopf algebra structure on the Laurent polynomials
  `A[T;T⁻¹]` when `A` is an `R`-Hopf algebra. When `A = R` this corresponds to the fact that `𝔾ₘ/R`
  is a group scheme.
-/

public section

noncomputable section

open HopfAlgebra

namespace MonoidAlgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]
variable {G : Type*} [Group G]

variable (R A G) in
set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := R)]
/-
**MonoidAlgebra.instHopfAlgebraStruct** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
形式化陈述：instHopfAlgebraStruct : HopfAlgebraStruct R A[G] where antipode
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instHopfAlgebraStruct : HopfAlgebraStruct R A[G] where
  antipode := Finsupp.lsum R (fun g ↦ lsingle g⁻¹ ∘ₗ antipode R) ∘ₗ (coeffLinearEquiv _).toLinearMap

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/-
**MonoidAlgebra.antipode_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：antipode_single (g : G) (a : A) : antipode R (single g a) = single g⁻¹ (an
tipode R a)
参数：g : G；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
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
· 使用引理 `MonoidAlgebra.single_zero`：single_zero (m : M) : (single m 0 : R[M]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma antipode_single (g : G) (a : A) : antipode R (single g a) = single g⁻¹ (antipode R a) := by
  simp [antipode]

open Coalgebra in
@[to_additive (dont_translate := R A)]
/-
**MonoidAlgebra.instHopfAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
形式化陈述：instHopfAlgebra : HopfAlgebra R A[G] where mul_antipode_rTensor_comul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instHopfAlgebra : HopfAlgebra R A[G] where
  mul_antipode_rTensor_comul := by
    ext a b : 2
    simpa [← (ℛ R b).eq] using congr(lsingle (R := R) (1 : G)
      $(sum_antipode_mul_eq_algebraMap_counit (ℛ R b)))
  mul_antipode_lTensor_comul := by
    ext a b : 2
    simpa [← (ℛ R b).eq] using congr(lsingle (R := R) (1 : G)
      $(sum_mul_antipode_eq_algebraMap_counit (ℛ R b)))

end MonoidAlgebra

namespace LaurentPolynomial

open Finsupp

variable (R A : Type*) [CommSemiring R] [Semiring A] [HopfAlgebra R A]

/-
**LaurentPolynomial.instHopfAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `LaurentPolynomial
`。
形式化陈述：instHopfAlgebra : HopfAlgebra R A[T;T⁻¹]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instHopfAlgebra : HopfAlgebra R A[T;T⁻¹] :=
  inferInstanceAs (HopfAlgebra R <| AddMonoidAlgebra A ℤ)

variable {R A}

@[simp]
/-
**LaurentPolynomial.antipode_C** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：antipode_C (a : A) : HopfAlgebra.antipode R (C a) = C (HopfAlgebra.antipod
e R a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LaurentPolynomial.single_eq_C`：single_eq_C (r : R) : .single 0 r = C r
· 使用定理 `AddMonoidAlgebra.antipode_single`：∀ {R : Type u_1} {A : Type u_2} [inst 
: CommSemiring R] [inst_1 : Semiring A] [inst_2 : HopfAlgebra R A] {G : Type u_3
}   [inst_3 : AddGroup…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `LaurentPolynomial.single_eq_C_mul_T`：single_eq_C_mul_T (r : R) (n : Int)
 : .single n r = C r * T n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem antipode_C (a : A) :
    HopfAlgebra.antipode R (C a) = C (HopfAlgebra.antipode R a) := by
  rw [← single_eq_C, AddMonoidAlgebra.antipode_single]
  simp

@[simp]
/-
**LaurentPolynomial.antipode_T** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomial`。
形式化陈述：antipode_T (n : Int) : HopfAlgebra.antipode R (T n : A[T;T⁻¹]) = T (-n)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.antipode_single`：∀ {R : Type u_1} {A : Type u_2} [inst 
: CommSemiring R] [inst_1 : Semiring A] [inst_2 : HopfAlgebra R A] {G : Type u_3
}   [inst_3 : AddGroup…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HopfAlgebra.antipode_one`：antipode_one : HopfAlgebra.antipode R (1 : A) 
= 1
· 使用定理 `LaurentPolynomial.single_eq_C_mul_T`：single_eq_C_mul_T (r : R) (n : Int)
 : .single n r = C r * T n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
theorem antipode_T (n : ℤ) :
    HopfAlgebra.antipode R (T n : A[T;T⁻¹]) = T (-n) := by
  unfold T
  rw [AddMonoidAlgebra.antipode_single]
  simp only [HopfAlgebra.antipode_one, single_eq_C_mul_T, map_one, one_mul]

@[simp]
/-
**LaurentPolynomial.antipode_C_mul_T** 是 Mathlib 中的一个定理，位于命名空间 `LaurentPolynomia
l`。
形式化陈述：antipode_C_mul_T (a : A) (n : Int) : HopfAlgebra.antipode R (C a * T n) = 
C (HopfAlgebra.antipode R a) * T (-n)
参数：a : A；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.antipode_single`：∀ {R : Type u_1} {A : Type u_2} [inst 
: CommSemiring R] [inst_1 : Semiring A] [inst_2 : HopfAlgebra R A] {G : Type u_3
}   [inst_3 : AddGroup…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem antipode_C_mul_T (a : A) (n : ℤ) :
    HopfAlgebra.antipode R (C a * T n) = C (HopfAlgebra.antipode R a) * T (-n) := by
  simp [← single_eq_C_mul_T]

end LaurentPolynomial

