/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Tactic.NoncommRing

/-! # Interactions between `R[X]` and `Rᵐᵒᵖ[X]`

This file contains the basic API for "pushing through" the isomorphism
`opRingEquiv : R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X]`.  It allows going back and forth between a polynomial ring
over a semiring and the polynomial ring over the opposite semiring. -/

@[expose] public section


open Polynomial

open MulOpposite

variable {R : Type*} [Semiring R]

noncomputable section

namespace Polynomial

/-- Ring isomorphism between `R[X]ᵐᵒᵖ` and `Rᵐᵒᵖ[X]` sending each coefficient of a polynomial
to the corresponding element of the opposite ring. -/
/-
**Polynomial.opRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：opRingEquiv (R : Type*) [Semiring R] : R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X]
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ring isomorphism between `R[X]ᵐᵒᵖ` and `Rᵐᵒᵖ[X]` sending each coefficient of a p
olynomial
to the corresponding element of the opposite ring.
-/
def opRingEquiv (R : Type*) [Semiring R] : R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X] :=
  ((toFinsuppIso R).op.trans <| AddMonoidAlgebra.opRingEquiv.trans <|
    AddMonoidAlgebra.mapDomainRingEquiv _ AddOpposite.opAddEquiv.symm).trans (toFinsuppIso _).symm

/-!  Lemmas to get started, using `opRingEquiv R` on the various expressions of
`Finsupp.single`: `monomial`, `C a`, `X`, `C a * X ^ n`. -/


set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Polynomial.opRingEquiv_op_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：opRingEquiv_op_monomial (n : Nat) (r : R) : opRingEquiv R (op (monomial n 
r : R[X])) = monomial n (op r)
参数：n : Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingEquiv.op_apply_apply`：∀ {α : Type u_7} {β : Type u_8} [inst : Add α]
 [inst_1 : Mul α] [inst_2 : Add β] [inst_3 : Mul β] (f : α ≃+* β)   (a : αᵐᵒᵖ), 
(RingEquiv.op …
· 使用定理 `Polynomial.toFinsuppIso_apply`：∀ (R : Type u) [inst : Semiring R] (self 
: Polynomial R), (Polynomial.toFinsuppIso R) self = self.toFinsupp
· 使用定理 `AddMonoidAlgebra.opRingEquiv_apply`：∀ {R : Type u_1} {M : Type u_2} [ins
t : Semiring R] [inst_1 : Add M] (a : (AddMonoidAlgebra R M)ᵐᵒᵖ),   AddMonoidAlg
ebra.opRingEquiv a =    …
· 使用定理 `AddMonoidAlgebra.mapDomainAddEquiv_single`：∀ {R : Type u_3} {M : Type u_
6} {N : Type u_7} [inst : Semiring R] [inst_1 : Add M] [inst_2 : Add N] (e : M ≃
 N) (r : R)   (m : M), (AddMono…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AddOpposite.opEquiv_apply`：∀ {α : Type u_1}, ⇑AddOpposite.opEquiv = AddO
pposite.op
· 使用定理 `AddMonoidAlgebra.mapAddEquiv_single`：∀ {R : Type u_3} {S : Type u_4} {M 
: Type u_6} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : Add M] (e : R ≃+
 S)   (r : R) (m : M), (A…
· 使用定理 `MulOpposite.opAddEquiv_apply`：∀ {α : Type u_2} [inst : Add α], ⇑MulOppos
ite.opAddEquiv = MulOpposite.op
· 使用定理 `AddMonoidAlgebra.mapDomainRingEquiv_single`：∀ {R : Type u_3} {M : Type u
_6} {N : Type u_7} [inst : Semiring R] [inst_1 : AddMonoid M] [inst_2 : AddMonoi
d N]   (e : M ≃+ N) (r : R) (m :…
· 使用定理 `AddOpposite.opAddEquiv_symm_apply`：∀ {M : Type u_1} [inst : AddCommMonoi
d M] (a : Mᵃᵒᵖ), AddOpposite.opAddEquiv.symm a = AddOpposite.unop a
· 使用定理 `Polynomial.toFinsuppIso_symm_apply`：∀ (R : Type u) [inst : Semiring R] (
toFinsupp : AddMonoidAlgebra R ℕ),   (Polynomial.toFinsuppIso R).symm toFinsupp 
= { toFinsupp := toFinsu…
· 使用定理 `Polynomial.coeff_ofFinsupp`：coeff_ofFinsupp (p) : coeff (⟨p⟩ : R[X]) = p
.coeff
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Lemmas to get started, using `opRingEquiv R` on the various expressions of
`Finsupp.single`: `monomial`, `C a`, `X`, `C a * X ^ n`.
-/
theorem opRingEquiv_op_monomial (n : ℕ) (r : R) :
    opRingEquiv R (op (monomial n r : R[X])) = monomial n (op r) := by
  ext; simp [opRingEquiv, ← ofFinsupp_single]

@[simp]
/-
**Polynomial.opRingEquiv_op_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：opRingEquiv_op_C (a : R) : opRingEquiv R (op (C a)) = C (op a)
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.opRingEquiv_op_monomial`：opRingEquiv_op_monomial (n : Nat) (r
 : R) : opRingEquiv R (op (monomial n r : R[X])) = monomial n (op r)
-/
theorem opRingEquiv_op_C (a : R) : opRingEquiv R (op (C a)) = C (op a) :=
  opRingEquiv_op_monomial 0 a

@[simp]
/-
**Polynomial.opRingEquiv_op_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：opRingEquiv_op_X : opRingEquiv R (op (X : R[X])) = X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.opRingEquiv_op_monomial`：opRingEquiv_op_monomial (n : Nat) (r
 : R) : opRingEquiv R (op (monomial n r : R[X])) = monomial n (op r)
-/
theorem opRingEquiv_op_X : opRingEquiv R (op (X : R[X])) = X :=
  opRingEquiv_op_monomial 1 1
/-
**Polynomial.opRingEquiv_op_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：opRingEquiv_op_C_mul_X_pow (r : R) (n : Nat) : opRingEquiv R (op (C r * X 
^ n : R[X])) = C (op r) * X ^ n
参数：r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `Polynomial.opRingEquiv_op_X`：opRingEquiv_op_X : opRingEquiv R (op (X : R
[X])) = X
· 使用定理 `Polynomial.opRingEquiv_op_C`：opRingEquiv_op_C (a : R) : opRingEquiv R (o
p (C a)) = C (op a)
· 使用定理 `Polynomial.X_pow_mul`：X_pow_mul {n : Nat} : X ^ n * p = p * X ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem opRingEquiv_op_C_mul_X_pow (r : R) (n : ℕ) :
    opRingEquiv R (op (C r * X ^ n : R[X])) = C (op r) * X ^ n := by
  simp only [X_pow_mul, op_mul, op_pow, map_mul, map_pow, opRingEquiv_op_X, opRingEquiv_op_C]

/-!  Lemmas to get started, using `(opRingEquiv R).symm` on the various expressions of
`Finsupp.single`: `monomial`, `C a`, `X`, `C a * X ^ n`. -/


@[simp]
/-
**Polynomial.opRingEquiv_symm_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：opRingEquiv_symm_monomial (n : Nat) (r : Rᵐᵒᵖ) : (opRingEquiv R).symm (mon
omial n r) = op (monomial n (unop r))
参数：n : Nat；r : Rᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `Polynomial.opRingEquiv_op_monomial`：opRingEquiv_op_monomial (n : Nat) (r
 : R) : opRingEquiv R (op (monomial n r : R[X])) = monomial n (op r)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Lemmas to get started, using `(opRingEquiv R).symm` on the various expressions o
f
`Finsupp.single`: `monomial`, `C a`, `X`, `C a * X ^ n`.
-/
theorem opRingEquiv_symm_monomial (n : ℕ) (r : Rᵐᵒᵖ) :
    (opRingEquiv R).symm (monomial n r) = op (monomial n (unop r)) :=
  (opRingEquiv R).injective (by simp)

@[simp]
/-
**Polynomial.opRingEquiv_symm_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：opRingEquiv_symm_C (a : Rᵐᵒᵖ) : (opRingEquiv R).symm (C a) = op (C (unop a
))
参数：a : Rᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.opRingEquiv_symm_monomial`：opRingEquiv_symm_monomial (n : Nat
) (r : Rᵐᵒᵖ) : (opRingEquiv R).symm (monomial n r) = op (monomial n (unop r))
-/
theorem opRingEquiv_symm_C (a : Rᵐᵒᵖ) : (opRingEquiv R).symm (C a) = op (C (unop a)) :=
  opRingEquiv_symm_monomial 0 a

@[simp]
/-
**Polynomial.opRingEquiv_symm_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：opRingEquiv_symm_X : (opRingEquiv R).symm (X : Rᵐᵒᵖ[X]) = op X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.opRingEquiv_symm_monomial`：opRingEquiv_symm_monomial (n : Nat
) (r : Rᵐᵒᵖ) : (opRingEquiv R).symm (monomial n r) = op (monomial n (unop r))
-/
theorem opRingEquiv_symm_X : (opRingEquiv R).symm (X : Rᵐᵒᵖ[X]) = op X :=
  opRingEquiv_symm_monomial 1 1
/-
**Polynomial.opRingEquiv_symm_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：opRingEquiv_symm_C_mul_X_pow (r : Rᵐᵒᵖ) (n : Nat) : (opRingEquiv R).symm (
C r * X ^ n : Rᵐᵒᵖ[X]) = op (C (unop r) * X ^ n)
参数：r : Rᵐᵒᵖ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.opRingEquiv_symm_monomial`：opRingEquiv_symm_monomial (n : Nat
) (r : Rᵐᵒᵖ) : (opRingEquiv R).symm (monomial n r) = op (monomial n (unop r))
-/
theorem opRingEquiv_symm_C_mul_X_pow (r : Rᵐᵒᵖ) (n : ℕ) :
    (opRingEquiv R).symm (C r * X ^ n : Rᵐᵒᵖ[X]) = op (C (unop r) * X ^ n) := by
  rw [C_mul_X_pow_eq_monomial, opRingEquiv_symm_monomial, C_mul_X_pow_eq_monomial]

/-!  Lemmas about more global properties of polynomials and opposites. -/

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Polynomial.coeff_opRingEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_opRingEquiv (p : R[X]ᵐᵒᵖ) (n : Nat) : (opRingEquiv R p).coeff n = op
 ((unop p).coeff n)
参数：p : R[X]ᵐᵒᵖ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `RingEquiv.op_apply_apply`：∀ {α : Type u_7} {β : Type u_8} [inst : Add α]
 [inst_1 : Mul α] [inst_2 : Add β] [inst_3 : Mul β] (f : α ≃+* β)   (a : αᵐᵒᵖ), 
(RingEquiv.op …
· 使用定理 `Polynomial.toFinsuppIso_apply`：∀ (R : Type u) [inst : Semiring R] (self 
: Polynomial R), (Polynomial.toFinsuppIso R) self = self.toFinsupp
· 使用定理 `AddMonoidAlgebra.opRingEquiv_apply`：∀ {R : Type u_1} {M : Type u_2} [ins
t : Semiring R] [inst_1 : Add M] (a : (AddMonoidAlgebra R M)ᵐᵒᵖ),   AddMonoidAlg
ebra.opRingEquiv a =    …
· 使用定理 `Polynomial.toFinsuppIso_symm_apply`：∀ (R : Type u) [inst : Semiring R] (
toFinsupp : AddMonoidAlgebra R ℕ),   (Polynomial.toFinsuppIso R).symm toFinsupp 
= { toFinsupp := toFinsu…
· 使用定理 `AddMonoidAlgebra.coeff_mapDomainRingEquiv`：∀ {R : Type u_3} {M : Type u_
6} {N : Type u_7} [inst : Semiring R] [inst_1 : AddMonoid M] [inst_2 : AddMonoid
 N]   (e : M ≃+ N) (x : AddMono…
· 使用定理 `AddOpposite.opAddEquiv_apply`：∀ {M : Type u_1} [inst : AddCommMonoid M] 
(a : M), AddOpposite.opAddEquiv a = AddOpposite.op a
· 使用定理 `AddMonoidAlgebra.coeff_mapAddEquiv`：∀ {R : Type u_3} {S : Type u_4} {M :
 Type u_6} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : Add M] (e : R ≃+ 
S)   (x : AddMonoidAlgeb…
· 使用定理 `AddMonoidAlgebra.coeff_mapDomainAddEquiv`：∀ {R : Type u_3} {M : Type u_6
} {N : Type u_7} [inst : Semiring R] [inst_1 : Add M] [inst_2 : Add N] (e : M ≃ 
N)   (x : AddMonoidAlgebra R M…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AddOpposite.opEquiv_symm_apply`：∀ {α : Type u_1}, ⇑AddOpposite.opEquiv.s
ymm = AddOpposite.unop
· 使用定理 `MulOpposite.opAddEquiv_apply`：∀ {α : Type u_2} [inst : Add α], ⇑MulOppos
ite.opAddEquiv = MulOpposite.op
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Lemmas about more global properties of polynomials and opposites.
-/
theorem coeff_opRingEquiv (p : R[X]ᵐᵒᵖ) (n : ℕ) :
    (opRingEquiv R p).coeff n = op ((unop p).coeff n) := by simp [opRingEquiv, coeff]

@[simp]
/-
**Polynomial.support_opRingEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_opRingEquiv (p : R[X]ᵐᵒᵖ) : (opRingEquiv R p).support = (unop p).s
upport
参数：p : R[X]ᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_opRingEquiv`：coeff_opRingEquiv (p : R[X]ᵐᵒᵖ) (n : Nat) 
: (opRingEquiv R p).coeff n = op ((unop p).coeff n)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_opRingEquiv (p : R[X]ᵐᵒᵖ) : (opRingEquiv R p).support = (unop p).support := by
  ext; simp

@[simp]
/-
**Polynomial.natDegree_opRingEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_opRingEquiv (p : R[X]ᵐᵒᵖ) : (opRingEquiv R p).natDegree = (unop 
p).natDegree
参数：p : R[X]ᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.nonempty_support_iff`：nonempty_support_iff : p.support.Nonemp
ty ↔ p != 0
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Polynomial.support_opRingEquiv`：support_opRingEquiv (p : R[X]ᵐᵒᵖ) : (opR
ingEquiv R p).support = (unop p).support
· 使用定理 `Polynomial.natDegree_eq_support_max'`：natDegree_eq_support_max' (h : p !
= 0) : p.natDegree = p.support.max' (nonempty_support_iff.mpr h)
· 使用定理 `Finset.max'.congr_simp`：∀ {α : Type u_2} [inst : LinearOrder α] (s s_1 :
 Finset α) (e_s : s = s_1) (H : s.Nonempty), s.max' H = s_1.max' ⋯
-/
theorem natDegree_opRingEquiv (p : R[X]ᵐᵒᵖ) : (opRingEquiv R p).natDegree = (unop p).natDegree := by
  by_cases p0 : p = 0
  · simp only [p0, map_zero, natDegree_zero, unop_zero]
  · simp only [p0, natDegree_eq_support_max', Ne, EmbeddingLike.map_eq_zero_iff, not_false_iff,
      support_opRingEquiv, unop_eq_zero_iff]

@[simp]
/-
**Polynomial.leadingCoeff_opRingEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_opRingEquiv (p : R[X]ᵐᵒᵖ) : (opRingEquiv R p).leadingCoeff = 
op (unop p).leadingCoeff
参数：p : R[X]ᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.coeff_opRingEquiv`：coeff_opRingEquiv (p : R[X]ᵐᵒᵖ) (n : Nat) 
: (opRingEquiv R p).coeff n = op ((unop p).coeff n)
· 使用定理 `Polynomial.natDegree_opRingEquiv`：natDegree_opRingEquiv (p : R[X]ᵐᵒᵖ) : 
(opRingEquiv R p).natDegree = (unop p).natDegree
-/
theorem leadingCoeff_opRingEquiv (p : R[X]ᵐᵒᵖ) :
    (opRingEquiv R p).leadingCoeff = op (unop p).leadingCoeff := by
  rw [leadingCoeff, coeff_opRingEquiv, natDegree_opRingEquiv, leadingCoeff]
/-
**Polynomial.isLeftCancelMulZero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isLeftCancelMulZero_iff : IsLeftCancelMulZero R[X] ↔ IsLeftCancelMulZero R
 ∧ IsCancelAdd R where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isLeftCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u_
3} [inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (
f : M₀ → M₀'),   Function.In…
· 使用定理 `Polynomial.C_injective`：C_injective : Injective (C : R -> R[X])
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Polynomial.X_mul_C`：X_mul_C (r : R) : X * C r = C r * X
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.C_add`：C_add : C (a + b) = C a + C b
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `_private.Mathlib.RingTheory.Polynomial.Opposites.0.Polynomial.isLeftCanc
elMulZero_iff._abel_1_5`：∀ {R : Type u_1} [inst : Semiring R] (a r : R),   Polyn
omial.C a * (Polynomial.X * (Polynomial.X * Polynomial.X)) + Polynomial.C a * (P
olyno…
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.coeff_X_one`：coeff_X_one : coeff (X : R[X]) 1 = 1
（共 40 条，此处仅展示前 30 条）
-/
theorem isLeftCancelMulZero_iff :
    IsLeftCancelMulZero R[X] ↔ IsLeftCancelMulZero R ∧ IsCancelAdd R where
  mp h := .intro (C_injective.isLeftCancelMulZero _ C_0 fun _ _ ↦ C_mul) <|
    have : IsLeftCancelAdd R := .mk fun a b c eq ↦ by
      nontriviality R
      let trinomial (r : R) : R[X] := a • X ^ 2 + r • X + C a
      have ht r : (X + C 1) * trinomial r = a • X ^ 3 + (a + r) • X ^ 2 + (a + r) • X + C a := by
        simp only [trinomial, mul_add, add_mul, ← C_mul', C_1, one_mul, ← mul_assoc, X_mul_C, C_add]
        noncomm_ring
      simpa [trinomial] using congr_arg (coeff · 1) <|
        h.1 (a₁ := trinomial b) (a₂ := trinomial c) (X_add_C_ne_zero 1) <| by simp_rw [ht, eq]
    AddCommMagma.IsLeftCancelAdd.toIsCancelAdd R
  mpr := fun ⟨_, _⟩ ↦ inferInstance
/-
**Polynomial.isRightCancelMulZero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isRightCancelMulZero_iff : IsRightCancelMulZero R[X] ↔ IsRightCancelMulZer
o R ∧ IsCancelAdd R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulOpposite.isLeftCancelMulZero_iff`：∀ {α : Type u_1} [inst : Mul α] [in
st_1 : Zero α], IsLeftCancelMulZero αᵐᵒᵖ ↔ IsRightCancelMulZero α
· 使用定理 `MulEquiv.isLeftCancelMulZero_iff`：isLeftCancelMulZero_iff (e : A ≃* B) :
 IsLeftCancelMulZero A ↔ IsLeftCancelMulZero B where mp _
· 使用定理 `Polynomial.isLeftCancelMulZero_iff`：isLeftCancelMulZero_iff : IsLeftCanc
elMulZero R[X] ↔ IsLeftCancelMulZero R ∧ IsCancelAdd R where mp h
· 使用定理 `MulOpposite.isCancelAdd_iff`：∀ {α : Type u_1} [inst : Add α], IsCancelAd
d αᵐᵒᵖ ↔ IsCancelAdd α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isRightCancelMulZero_iff :
    IsRightCancelMulZero R[X] ↔ IsRightCancelMulZero R ∧ IsCancelAdd R := by
  rw [← MulOpposite.isLeftCancelMulZero_iff, (opRingEquiv R).isLeftCancelMulZero_iff,
    isLeftCancelMulZero_iff, MulOpposite.isLeftCancelMulZero_iff, MulOpposite.isCancelAdd_iff]
/-
**Polynomial.isCancelMulZero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R], IsCancelMulZero (Polynomial R) ↔ IsC
ancelMulZero R ∧ IsCancelAdd R
参数：Polynomial R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_and_and_comm`：∀ {a b c d : Prop}, (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem isCancelMulZero_iff :
    IsCancelMulZero R[X] ↔ IsCancelMulZero R ∧ IsCancelAdd R := by
  simp_rw [isCancelMulZero_iff, isLeftCancelMulZero_iff, isRightCancelMulZero_iff]
  rw [and_and_and_comm, and_self]
/-
**Polynomial.isDomain_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isDomain_iff : IsDomain R[X] ↔ IsDomain R ∧ IsCancelAdd R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isDomain_iff : IsDomain R[X] ↔ IsDomain R ∧ IsCancelAdd R := by
  simp_rw [isDomain_iff_cancelMulZero_and_nontrivial, nontrivial_iff,
    Polynomial.isCancelMulZero_iff, and_right_comm]

end Polynomial

