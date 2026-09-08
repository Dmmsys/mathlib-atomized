/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change of polynomial algebras

Given `[CommSemiring R] [Semiring A] [Algebra R A]` we show `A[X] ≃ₐ[R] (A ⊗[R] R[X])`.
-/

@[expose] public section

-- This file should not become entangled with `RingTheory/MatrixAlgebra`.
assert_not_exists Matrix

universe u v w

open Polynomial TensorProduct

open Algebra.TensorProduct (algHomOfLinearMapTensorProduct includeLeft)

noncomputable section

variable (R S A : Type*)
variable [CommSemiring R] [CommSemiring S]
variable [Semiring A] [Algebra R A] [Algebra R S] [Algebra S A] [IsScalarTower R S A]

namespace PolyEquivTensor

/-- (Implementation detail).
The function underlying `A ⊗[R] R[X] →ₐ[R] A[X]`,
as a bilinear function of two arguments.
-/
/-
**PolyEquivTensor.toFunBilinear** 是 Mathlib 中的一个定义，位于命名空间 `PolyEquivTensor`。
形式化陈述：toFunBilinear : A ->ₗ[A] R[X] ->ₗ[R] A[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation detail).
The function underlying `A ⊗[R] R[X] →ₐ[R] A[X]`,
as a bilinear function of two arguments.
-/
def toFunBilinear : A →ₗ[A] R[X] →ₗ[R] A[X] :=
  LinearMap.toSpanSingleton A _ (aeval (Polynomial.X : A[X])).toLinearMap
/-
**PolyEquivTensor.toFunBilinear_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `PolyEquiv
Tensor`。
形式化陈述：toFunBilinear_apply_apply (a : A) (p : R[X]) : toFunBilinear R A a p = a •
 (aeval X) p
参数：a : A；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem toFunBilinear_apply_apply (a : A) (p : R[X]) :
    toFunBilinear R A a p = a • (aeval X) p := rfl
/-
**PolyEquivTensor.toFunBilinear_apply_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `PolyEqu
ivTensor`。
形式化陈述：∀ (R : Type u_1) (A : Type u_3) [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : Algebra R A] (a : A)   (p : Polynomial R), ((PolyEquivTensor.toFun
Bilinear R A) a) p = a • Polynomial.map (algebraMap R A) p
参数：R : Type u_1；A : Type u_3；a : A；p : Polynomial R；(PolyEquivTensor.toFunBiline
ar R A) a；algebraMap R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] theorem toFunBilinear_apply_eq_smul (a : A) (p : R[X]) :
    toFunBilinear R A a p = a • p.map (algebraMap R A) := rfl
/-
**PolyEquivTensor.toFunBilinear_apply_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `PolyEqui
vTensor`。
形式化陈述：toFunBilinear_apply_eq_sum (a : A) (p : R[X]) : toFunBilinear R A a p = p.
sum fun n r => monomial n (a * algebraMap R A r)
参数：a : A；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PolyEquivTensor.toFunBilinear_apply_eq_smul`：∀ (R : Type u_1) (A : Type 
u_3) [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (a : A
)   (p : Polynomial R), ((PolyEqu…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.sum_monomial_eq`：∀ {R : Type u} [inst : Semiring R] (p : Poly
nomial R), (p.sum fun n a => (Polynomial.monomial n) a) = p
· 使用定理 `Polynomial.sum.eq_1`：∀ {R : Type u} [inst : Semiring R] {S : Type u_1} [
inst_1 : AddCommMonoid S] (p : Polynomial R) (f : ℕ → R → S),   p.sum f = ∑ n ∈ 
p.support…
· 使用定理 `Polynomial.map_sum`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S) {ι : Type u_1}   (g : ι → Polynomial R) (s : Fin
set ι), …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.map_monomial`：map_monomial {n a} : (monomial n a).map f = mon
omial n (f a)
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFunBilinear_apply_eq_sum (a : A) (p : R[X]) :
    toFunBilinear R A a p = p.sum fun n r ↦ monomial n (a * algebraMap R A r) := by
  conv_lhs => rw [toFunBilinear_apply_eq_smul, ← p.sum_monomial_eq, sum, Polynomial.map_sum]
  simp [Finset.smul_sum, sum, ← smul_eq_mul]

/-- (Implementation detail).
The function underlying `A ⊗[R] R[X] →ₐ[R] A[X]`,
as a linear map.
-/
/-
**PolyEquivTensor.toFunLinear** 是 Mathlib 中的一个定义，位于命名空间 `PolyEquivTensor`。
形式化陈述：toFunLinear : A otimes[R] R[X] ->ₗ[R] A[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation detail).
The function underlying `A ⊗[R] R[X] →ₐ[R] A[X]`,
as a linear map.
-/
def toFunLinear : A ⊗[R] R[X] →ₗ[R] A[X] :=
  TensorProduct.lift (toFunBilinear R A)

@[simp]
/-
**PolyEquivTensor.toFunLinear_tmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `PolyEquivTen
sor`。
形式化陈述：toFunLinear_tmul_apply (a : A) (p : R[X]) : toFunLinear R A (a otimesₜ[R] 
p) = toFunBilinear R A a p
参数：a : A；p : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFunLinear_tmul_apply (a : A) (p : R[X]) :
    toFunLinear R A (a ⊗ₜ[R] p) = toFunBilinear R A a p :=
  rfl

-- We apparently need to provide the decidable instance here
-- in order to successfully rewrite by this lemma.
/-
**PolyEquivTensor.toFunLinear_mul_tmul_mul_aux_1** 是 Mathlib 中的一个定理，位于命名空间 `Poly
EquivTensor`。
形式化陈述：toFunLinear_mul_tmul_mul_aux_1 (p : R[X]) (k : Nat) (h : Decidable ¬p.coef
f k = 0) (a : A) : ite (¬coeff p k = 0) (a * (algebraMap R A) (coeff p k)) 0 = a
 * (algebraMap R A) (coeff p k)
参数：p : R[X]；k : Nat；h : Decidable ¬p.coeff k = 0；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `not_not_intro`：∀ {p : Prop}, p → ¬¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem toFunLinear_mul_tmul_mul_aux_1 (p : R[X]) (k : ℕ) (h : Decidable ¬p.coeff k = 0) (a : A) :
    ite (¬coeff p k = 0) (a * (algebraMap R A) (coeff p k)) 0 =
    a * (algebraMap R A) (coeff p k) := by split_ifs <;> simp [*]
/-
**PolyEquivTensor.toFunLinear_mul_tmul_mul_aux_2** 是 Mathlib 中的一个定理，位于命名空间 `Poly
EquivTensor`。
形式化陈述：toFunLinear_mul_tmul_mul_aux_2 (k : Nat) (a₁ a₂ : A) (p₁ p₂ : R[X]) : a₁ *
 a₂ * (algebraMap R A) ((p₁ * p₂).coeff k) = (Finset.antidiagonal k).sum fun x =
> a₁ * (algebraMap R A) (coeff p₁ x.1) * (a₂ * (algebraMap R A) (coeff p₂ x.2))
参数：k : Nat；a₁ a₂ : A；p₁ p₂ : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFunLinear_mul_tmul_mul_aux_2 (k : ℕ) (a₁ a₂ : A) (p₁ p₂ : R[X]) :
    a₁ * a₂ * (algebraMap R A) ((p₁ * p₂).coeff k) =
      (Finset.antidiagonal k).sum fun x =>
        a₁ * (algebraMap R A) (coeff p₁ x.1) * (a₂ * (algebraMap R A) (coeff p₂ x.2)) := by
  simp_rw [mul_assoc, Algebra.commutes, ← Finset.mul_sum, mul_assoc, ← Finset.mul_sum]
  congr
  simp_rw [Algebra.commutes (coeff p₂ _), coeff_mul, map_sum, map_mul]
/-
**PolyEquivTensor.toFunLinear_mul_tmul_mul** 是 Mathlib 中的一个定理，位于命名空间 `PolyEquivT
ensor`。
形式化陈述：toFunLinear_mul_tmul_mul (a₁ a₂ : A) (p₁ p₂ : R[X]) : (toFunLinear R A) ((
a₁ * a₂) otimesₜ[R] (p₁ * p₂)) = (toFunLinear R A) (a₁ otimesₜ[R] p₁) * (toFunLi
near R A) (a₂ otimesₜ[R] p₂)
参数：a₁ a₂ : A；p₁ p₂ : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PolyEquivTensor.toFunBilinear_apply_eq_sum`：toFunBilinear_apply_eq_sum (
a : A) (p : R[X]) : toFunBilinear R A a p = p.sum fun n r => monomial n (a * alg
ebraMap R A r)
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_sum`：coeff_sum [Semiring S] (n : Nat) (f : Nat -> R -> 
S[X]) : coeff (p.sum f) n = p.sum fun a b => coeff (f a b) n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ite_zero_mul`：ite_zero_mul : ite P a 0 * b = ite P (a * b) 0
· 使用引理 `mul_ite_zero`：mul_ite_zero : a * ite P b 0 = ite P (a * b) 0
· 使用定理 `PolyEquivTensor.toFunLinear_mul_tmul_mul_aux_1`：toFunLinear_mul_tmul_mul
_aux_1 (p : R[X]) (k : Nat) (h : Decidable ¬p.coeff k = 0) (a : A) : ite (¬coeff
 p k = 0) (a * (algebraMap R A) (coe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PolyEquivTensor.toFunLinear_mul_tmul_mul_aux_2`：toFunLinear_mul_tmul_mul
_aux_2 (k : Nat) (a₁ a₂ : A) (p₁ p₂ : R[X]) : a₁ * a₂ * (algebraMap R A) ((p₁ * 
p₂).coeff k) = (Finset.antidiagonal …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFunLinear_mul_tmul_mul (a₁ a₂ : A) (p₁ p₂ : R[X]) :
    (toFunLinear R A) ((a₁ * a₂) ⊗ₜ[R] (p₁ * p₂)) =
      (toFunLinear R A) (a₁ ⊗ₜ[R] p₁) * (toFunLinear R A) (a₂ ⊗ₜ[R] p₂) := by
  classical
    simp only [toFunLinear_tmul_apply, toFunBilinear_apply_eq_sum]
    ext k
    simp_rw [coeff_sum, coeff_monomial, sum_def, Finset.sum_ite_eq', mem_support_iff, Ne]
    conv_rhs => rw [coeff_mul]
    simp_rw [finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq', mem_support_iff, Ne, mul_ite,
      mul_zero, ite_mul, zero_mul]
    simp_rw [← ite_zero_mul (¬coeff p₁ _ = 0) (a₁ * (algebraMap R A) (coeff p₁ _))]
    simp_rw [← mul_ite_zero (¬coeff p₂ _ = 0) _ (_ * _)]
    simp_rw [toFunLinear_mul_tmul_mul_aux_1, toFunLinear_mul_tmul_mul_aux_2]
/-
**PolyEquivTensor.toFunLinear_one_tmul_one** 是 Mathlib 中的一个定理，位于命名空间 `PolyEquivT
ensor`。
形式化陈述：toFunLinear_one_tmul_one : toFunLinear R A (1 otimesₜ[R] 1) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PolyEquivTensor.toFunLinear_tmul_apply`：toFunLinear_tmul_apply (a : A) (
p : R[X]) : toFunLinear R A (a otimesₜ[R] p) = toFunBilinear R A a p
· 使用定理 `PolyEquivTensor.toFunBilinear_apply_apply`：toFunBilinear_apply_apply (a 
: A) (p : R[X]) : toFunBilinear R A a p = a • (aeval X) p
· 使用定理 `Polynomial.aeval_one`：aeval_one : aeval x (1 : R[X]) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem toFunLinear_one_tmul_one :
    toFunLinear R A (1 ⊗ₜ[R] 1) = 1 := by
  rw [toFunLinear_tmul_apply, toFunBilinear_apply_apply, Polynomial.aeval_one, one_smul]

/-- (Implementation detail).
The algebra homomorphism `A ⊗[R] R[X] →ₐ[R] A[X]`.
-/
/-
**PolyEquivTensor.toFunAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `PolyEquivTensor`。
形式化陈述：toFunAlgHom : A otimes[R] R[X] ->ₐ[R] A[X]
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PolyEquivTensor.toFunLinear_mul_tmul_mul`：toFunLinear_mul_tmul_mul (a₁ a
₂ : A) (p₁ p₂ : R[X]) : (toFunLinear R A) ((a₁ * a₂) otimesₜ[R] (p₁ * p₂)) = (to
FunLinear R A) (a₁ otimesₜ[R] …
· 使用定理 `PolyEquivTensor.toFunLinear_one_tmul_one`：toFunLinear_one_tmul_one : toF
unLinear R A (1 otimesₜ[R] 1) = 1

--- 原说明 ---
(Implementation detail).
The algebra homomorphism `A ⊗[R] R[X] →ₐ[R] A[X]`.
-/
def toFunAlgHom : A ⊗[R] R[X] →ₐ[R] A[X] :=
  algHomOfLinearMapTensorProduct (toFunLinear R A) (toFunLinear_mul_tmul_mul R A)
    (toFunLinear_one_tmul_one R A)
/-
**PolyEquivTensor.toFunAlgHom_apply_tmul_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `Poly
EquivTensor`。
形式化陈述：∀ (R : Type u_1) (A : Type u_3) [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : Algebra R A] (a : A)   (p : Polynomial R), (PolyEquivTensor.toFunA
lgHom R A) (a ⊗ₜ[R] p) = a • Polynomial.map (algebraMap R A) p
参数：R : Type u_1；A : Type u_3；a : A；p : Polynomial R；PolyEquivTensor.toFunAlgHom 
R A；a ⊗ₜ[R] p；algebraMap R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toFunAlgHom_apply_tmul_eq_smul (a : A) (p : R[X]) :
    toFunAlgHom R A (a ⊗ₜ[R] p) = a • p.map (algebraMap R A) := rfl
/-
**PolyEquivTensor.toFunAlgHom_apply_tmul** 是 Mathlib 中的一个定理，位于命名空间 `PolyEquivTen
sor`。
形式化陈述：toFunAlgHom_apply_tmul (a : A) (p : R[X]) : toFunAlgHom R A (a otimesₜ[R] 
p) = p.sum fun n r => monomial n (a * (algebraMap R A) r)
参数：a : A；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolyEquivTensor.toFunBilinear_apply_eq_sum`：toFunBilinear_apply_eq_sum (
a : A) (p : R[X]) : toFunBilinear R A a p = p.sum fun n r => monomial n (a * alg
ebraMap R A r)
-/
theorem toFunAlgHom_apply_tmul (a : A) (p : R[X]) :
    toFunAlgHom R A (a ⊗ₜ[R] p) = p.sum fun n r => monomial n (a * (algebraMap R A) r) :=
  toFunBilinear_apply_eq_sum R A _ _

/-- (Implementation detail.)

The bare function `A[X] → A ⊗[R] R[X]`.
(We don't need to show that it's an algebra map, thankfully --- just that it's an inverse.)
-/
/-
**PolyEquivTensor.invFun** 是 Mathlib 中的一个定义，位于命名空间 `PolyEquivTensor`。
形式化陈述：invFun (p : A[X]) : A otimes[R] R[X]
参数：p : A[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation detail.)

The bare function `A[X] → A ⊗[R] R[X]`.
(We don't need to show that it's an algebra map, thankfully --- just that it's a
n inverse.)
-/
def invFun (p : A[X]) : A ⊗[R] R[X] :=
  p.eval₂ (includeLeft : A →ₐ[R] A ⊗[R] R[X]) ((1 : A) ⊗ₜ[R] (X : R[X]))

@[simp]
/-
**PolyEquivTensor.invFun_add** 是 Mathlib 中的一个定理，位于命名空间 `PolyEquivTensor`。
形式化陈述：invFun_add {p q} : invFun R A (p + q) = invFun R A p + invFun R A q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_add`：eval₂_add : (p + q).eval₂ f x = p.eval₂ f x + q.ev
al₂ f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invFun_add {p q} : invFun R A (p + q) = invFun R A p + invFun R A q := by
  simp only [invFun, eval₂_add]
/-
**PolyEquivTensor.invFun_monomial** 是 Mathlib 中的一个定理，位于命名空间 `PolyEquivTensor`。
形式化陈述：invFun_monomial (n : Nat) (a : A) : invFun R A (monomial n a) = (a otimesₜ
[R] 1) * 1 otimesₜ[R] X ^ n
参数：n : Nat；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eval₂_monomial`：eval₂_monomial {n : Nat} {r : R} : (monomial 
n r).eval₂ f x = f r * x ^ n
-/
theorem invFun_monomial (n : ℕ) (a : A) :
    invFun R A (monomial n a) = (a ⊗ₜ[R] 1) * 1 ⊗ₜ[R] X ^ n :=
  eval₂_monomial _ _
/-
**PolyEquivTensor.left_inv** 是 Mathlib 中的一个定理，位于命名空间 `PolyEquivTensor`。
形式化陈述：left_inv (x : A otimes R[X]) : invFun R A ((toFunAlgHom R A) x) = x
参数：x : A otimes R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.eval₂_zero`：eval₂_zero : (0 : R[X]).eval₂ f x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PolyEquivTensor.toFunAlgHom_apply_tmul`：toFunAlgHom_apply_tmul (a : A) (
p : R[X]) : toFunAlgHom R A (a otimesₜ[R] p) = p.sum fun n r => monomial n (a * 
(algebraMap R A) r)
· 使用定理 `Polynomial.eval₂_sum`：eval₂_sum (p : T[X]) (g : Nat -> T -> R[X]) (x : S
) : (p.sum g).eval₂ f x = p.sum fun n a => (g n a).eval₂ f x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval₂_monomial`：eval₂_monomial {n : Nat} {r : R} : (monomial 
n r).eval₂ f x = f r * x ^ n
· 使用定理 `Algebra.TensorProduct.tmul_pow`：tmul_pow (a : A) (b : B) (k : Nat) : a o
timesₜ[R] b ^ k = (a ^ k) otimesₜ[R] (b ^ k)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.sum_C_mul_X_pow_eq`：sum_C_mul_X_pow_eq (p : R[X]) : (p.sum fu
n n a => C a * X ^ n) = p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
（共 33 条，此处仅展示前 30 条）
-/
theorem left_inv (x : A ⊗ R[X]) : invFun R A ((toFunAlgHom R A) x) = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [invFun]
  · intro a p
    dsimp only [invFun]
    rw [toFunAlgHom_apply_tmul, eval₂_sum]
    simp_rw [eval₂_monomial, AlgHom.coe_toRingHom, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul, ← Algebra.commutes, ← Algebra.smul_def, smul_tmul, sum_def, ← tmul_sum]
    conv_rhs => rw [← sum_C_mul_X_pow_eq p]
    simp only [Algebra.smul_def]
    rfl
  · intro p q hp hq
    simp only [map_add, invFun_add, hp, hq]
/-
**PolyEquivTensor.right_inv** 是 Mathlib 中的一个定理，位于命名空间 `PolyEquivTensor`。
形式化陈述：right_inv (x : A[X]) : (toFunAlgHom R A) (invFun R A x) = x
参数：x : A[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PolyEquivTensor.invFun_add`：invFun_add {p q} : invFun R A (p + q) = invF
un R A p + invFun R A q
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PolyEquivTensor.invFun_monomial`：invFun_monomial (n : Nat) (a : A) : inv
Fun R A (monomial n a) = (a otimesₜ[R] 1) * 1 otimesₜ[R] X ^ n
· 使用定理 `Algebra.TensorProduct.tmul_pow`：tmul_pow (a : A) (b : B) (k : Nat) : a o
timesₜ[R] b ^ k = (a ^ k) otimesₜ[R] (b ^ k)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Algebra.TensorProduct.tmul_mul_tmul`：tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : 
B) : a₁ otimesₜ[R] b₁ * a₂ otimesₜ[R] b₂ = (a₁ * a₂) otimesₜ[R] (b₁ * b₂)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `PolyEquivTensor.toFunAlgHom_apply_tmul`：toFunAlgHom_apply_tmul (a : A) (
p : R[X]) : toFunAlgHom R A (a otimesₜ[R] p) = p.sum fun n r => monomial n (a * 
(algebraMap R A) r)
· 使用定理 `Polynomial.X_pow_eq_monomial`：X_pow_eq_monomial (n) : X ^ n = monomial n
 (1 : R)
· 使用定理 `Polynomial.sum_monomial_index`：sum_monomial_index {S : Type*} [AddCommMo
noid S] {n : Nat} (a : R) (f : Nat -> R -> S) (hf : f n 0 = 0) : (monomial n a :
 R[X]).sum f = f n …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.monomial_zero_right`：monomial_zero_right (n : Nat) : monomial
 n (0 : R) = 0
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
（共 31 条，此处仅展示前 30 条）
-/
theorem right_inv (x : A[X]) : (toFunAlgHom R A) (invFun R A x) = x := by
  refine Polynomial.induction_on' x ?_ ?_
  · intro p q hp hq
    simp only [invFun_add, map_add, hp, hq]
  · intro n a
    rw [invFun_monomial, Algebra.TensorProduct.tmul_pow,
        one_pow, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, toFunAlgHom_apply_tmul,
        X_pow_eq_monomial, sum_monomial_index] <;>
      simp

/-- (Implementation detail)

The equivalence, ignoring the algebra structure, `(A ⊗[R] R[X]) ≃ A[X]`.
-/
/-
**PolyEquivTensor.equiv** 是 Mathlib 中的一个定义，位于命名空间 `PolyEquivTensor`。
形式化陈述：equiv : A otimes[R] R[X] ≃ A[X] where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PolyEquivTensor.left_inv`：left_inv (x : A otimes R[X]) : invFun R A ((to
FunAlgHom R A) x) = x
· 使用定理 `PolyEquivTensor.right_inv`：right_inv (x : A[X]) : (toFunAlgHom R A) (inv
Fun R A x) = x

--- 原说明 ---
(Implementation detail)

The equivalence, ignoring the algebra structure, `(A ⊗[R] R[X]) ≃ A[X]`.
-/
def equiv : A ⊗[R] R[X] ≃ A[X] where
  toFun := toFunAlgHom R A
  invFun := invFun R A
  left_inv := left_inv R A
  right_inv := right_inv R A

end PolyEquivTensor

open PolyEquivTensor

/-- The `R`-algebra isomorphism `A[X] ≃ₐ[R] (A ⊗[R] R[X])`.
-/
/-
**polyEquivTensor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：polyEquivTensor : A[X] ≃ₐ[R] A otimes[R] R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-algebra isomorphism `A[X] ≃ₐ[R] (A ⊗[R] R[X])`.
-/
def polyEquivTensor : A[X] ≃ₐ[R] A ⊗[R] R[X] :=
  AlgEquiv.symm { PolyEquivTensor.toFunAlgHom R A, PolyEquivTensor.equiv R A with }

@[simp]
/-
**polyEquivTensor_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：polyEquivTensor_apply (p : A[X]) : polyEquivTensor R A p = p.eval₂ (includ
eLeft : A ->ₐ[R] A otimes[R] R[X]) ((1 : A) otimesₜ[R] (X : R[X]))
参数：p : A[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem polyEquivTensor_apply (p : A[X]) :
    polyEquivTensor R A p =
      p.eval₂ (includeLeft : A →ₐ[R] A ⊗[R] R[X]) ((1 : A) ⊗ₜ[R] (X : R[X])) :=
  rfl

@[simp]
/-
**polyEquivTensor_symm_apply_tmul_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：polyEquivTensor_symm_apply_tmul_eq_smul (a : A) (p : R[X]) : (polyEquivTen
sor R A).symm (a otimesₜ p) = a • p.map (algebraMap R A)
参数：a : A；p : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem polyEquivTensor_symm_apply_tmul_eq_smul (a : A) (p : R[X]) :
    (polyEquivTensor R A).symm (a ⊗ₜ p) = a • p.map (algebraMap R A) := rfl
/-
**polyEquivTensor_symm_apply_tmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：polyEquivTensor_symm_apply_tmul (a : A) (p : R[X]) : (polyEquivTensor R A)
.symm (a otimesₜ p) = p.sum fun n r => monomial n (a * algebraMap R A r)
参数：a : A；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolyEquivTensor.toFunAlgHom_apply_tmul`：toFunAlgHom_apply_tmul (a : A) (
p : R[X]) : toFunAlgHom R A (a otimesₜ[R] p) = p.sum fun n r => monomial n (a * 
(algebraMap R A) r)
-/
theorem polyEquivTensor_symm_apply_tmul (a : A) (p : R[X]) :
    (polyEquivTensor R A).symm (a ⊗ₜ p) = p.sum fun n r => monomial n (a * algebraMap R A r) :=
  toFunAlgHom_apply_tmul _ _ _ _

section

variable (A : Type*) [CommSemiring A] [Algebra R A]

/-- The `A`-algebra isomorphism `A[X] ≃ₐ[A] A ⊗[R] R[X]` (when `A` is commutative). -/
/-
**polyEquivTensor'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：polyEquivTensor' : A[X] ≃ₐ[A] A otimes[R] R[X] where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `A`-algebra isomorphism `A[X] ≃ₐ[A] A ⊗[R] R[X]` (when `A` is commutative).
-/
def polyEquivTensor' : A[X] ≃ₐ[A] A ⊗[R] R[X] where
  __ := polyEquivTensor R A
  commutes' a := by simp

/-- `polyEquivTensor' R A` is the same as `polyEquivTensor R A` as a function. -/
/-
**coe_polyEquivTensor'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (R : Type u_1) [inst : CommSemiring R] (A : Type u_4) [inst_1 : CommSemi
ring A] [inst_2 : Algebra R A],   ⇑(polyEquivTensor' R A) = ⇑(polyEquivTensor R 
A)
参数：R : Type u_1；A : Type u_4；polyEquivTensor' R A；polyEquivTensor R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
`polyEquivTensor' R A` is the same as `polyEquivTensor R A` as a function.
-/
@[simp] theorem coe_polyEquivTensor' : ⇑(polyEquivTensor' R A) = polyEquivTensor R A := rfl
/-
**coe_polyEquivTensor'_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (R : Type u_1) [inst : CommSemiring R] (A : Type u_4) [inst_1 : CommSemi
ring A] [inst_2 : Algebra R A],   ⇑(polyEquivTensor' R A).symm = ⇑(polyEquivTens
or R A).symm
参数：R : Type u_1；A : Type u_4；polyEquivTensor' R A；polyEquivTensor R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
`polyEquivTensor' R A` is the same as `polyEquivTensor R A` as a function.
-/
@[simp] theorem coe_polyEquivTensor'_symm :
    ⇑(polyEquivTensor' R A).symm = (polyEquivTensor R A).symm := rfl

end

/-- If `A` is an `R`-algebra, then `A[X]` is an `R[X]` algebra.
This gives a diamond for `Algebra R[X] R[X][X]`, so this is not a global instance. -/
/-
**Polynomial.algebra** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：(R : Type u_1) →   (A : Type u_3) →     [inst : CommSemiring R] → [inst_1 
: Semiring A] → [Algebra R A] → Algebra (Polynomial R) (Polynomial A)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is an `R`-algebra, then `A[X]` is an `R[X]` algebra.
This gives a diamond for `Algebra R[X] R[X][X]`, so this is not a global instanc
e.
-/
@[reducible] def Polynomial.algebra : Algebra R[X] A[X] :=
  (mapRingHom (algebraMap R A)).toAlgebra' fun _ _ ↦ by
    ext; rw [coeff_mul, ← Finset.Nat.sum_antidiagonal_swap, coeff_mul]; simp [Algebra.commutes]

attribute [local instance] Polynomial.algebra

@[simp]
/-
**Polynomial.algebraMap_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.algebraMap_def : algebraMap R[X] A[X] = mapRingHom (algebraMap 
R A)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Polynomial.algebraMap_def : algebraMap R[X] A[X] = mapRingHom (algebraMap R A) := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower R S[X] A[X] :=
  have : IsScalarTower S S[X] A[X] := .of_algebraMap_eq' (mapRingHom_comp_C _).symm
  .to₁₃₄ _ S _ _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower R[X] S[X] A[X] := .of_algebraMap_eq' <|
  congr(mapRingHom $(IsScalarTower.algebraMap_eq R S A)).trans (mapRingHom_comp ..).symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FaithfulSMul R A] : FaithfulSMul R[X] A[X] :=
  (faithfulSMul_iff_algebraMap_injective ..).mpr
    (map_injective _ <| FaithfulSMul.algebraMap_injective ..)

variable {S : Type*} [CommSemiring S] [Algebra R S]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra.IsPushout R S R[X] S[X] where
  out := .of_equiv (polyEquivTensor' R S).symm fun _ ↦
    (polyEquivTensor_symm_apply_tmul_eq_smul ..).trans <| one_smul ..
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra.IsPushout R R[X] S S[X] := .symm inferInstance
