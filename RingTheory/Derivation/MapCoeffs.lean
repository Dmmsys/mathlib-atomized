/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
module

public import Mathlib.RingTheory.Derivation.DifferentialRing
public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.FieldTheory.Separable

/-!
# Coefficient-wise derivation on polynomials

In this file we define applying a derivation on the coefficients of a polynomial,
show this forms a derivation, and prove `apply_eval_eq`, which shows that for a derivation `D`,
`D(p(x)) = (D.mapCoeffs p)(x) + D(x) * p'(x)`. `apply_aeval_eq` and `apply_aeval_eq'`
are generalizations of that for algebras. We also have a special case for `DifferentialAlgebra`s.
-/

@[expose] public section

noncomputable section

open Polynomial Module

namespace Derivation

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M]
  [Module A M] [Module R M] (d : Derivation R A M)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
The `R`-derivation from `A[X]` to `M[X]` which applies the derivative to each
of the coefficients.
-/
/-
**Derivation.mapCoeffs** 是 Mathlib 中的一个定义，位于命名空间 `Derivation`。
形式化陈述：mapCoeffs : Derivation R A[X] (PolynomialModule A M) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-derivation from `A[X]` to `M[X]` which applies the derivative to each
of the coefficients.
-/
def mapCoeffs : Derivation R A[X] (PolynomialModule A M) where
  __ := (PolynomialModule.map A d.toLinearMap).comp
    PolynomialModule.equivPolynomial.symm.toLinearMap
  map_one_eq_zero' := by simp
  leibniz' p q := by
    dsimp
    induction p using Polynomial.induction_on' with
    | add => simp only [add_mul, map_add, add_smul, smul_add, add_add_add_comm, *]
    | monomial n a =>
      induction q using Polynomial.induction_on' with
      | add => simp only [mul_add, map_add, add_smul, smul_add, add_add_add_comm, *]
      | monomial m b => ext; simp [Polynomial.monomial_mul_monomial, add_comm]

@[simp]
/-
**Derivation.mapCoeffs_apply** 是 Mathlib 中的一个引理，位于命名空间 `Derivation`。
形式化陈述：mapCoeffs_apply (p : A[X]) (i) : (d.mapCoeffs p).coeff i = d (coeff p i)
参数：p : A[X]；i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapCoeffs_apply (p : A[X]) (i) : (d.mapCoeffs p).coeff i = d (coeff p i) := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Derivation.mapCoeffs_monomial** 是 Mathlib 中的一个引理，位于命名空间 `Derivation`。
形式化陈述：mapCoeffs_monomial (n : Nat) (x : A) : d.mapCoeffs (monomial n x) = .singl
e A n (d x)
参数：n : Nat；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynomialModule.ext`：∀ {R : Type u_2} {M : Type u_3} [inst : CommRing R
] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {x y : PolynomialModu
le R M}, x…
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapCoeffs_monomial (n : ℕ) (x : A) :
    d.mapCoeffs (monomial n x) = .single A n (d x) := by
  ext; simp [coeff_monomial, apply_ite d, Finsupp.single_apply]

@[simp]
/-
**Derivation.mapCoeffs_X** 是 Mathlib 中的一个引理，位于命名空间 `Derivation`。
形式化陈述：mapCoeffs_X : d.mapCoeffs (X : A[X]) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Derivation.mapCoeffs_monomial`：mapCoeffs_monomial (n : Nat) (x : A) : d.
mapCoeffs (monomial n x) = .single A n (d x)
· 使用定理 `Derivation.map_one_eq_zero`：map_one_eq_zero : D 1 = 0
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapCoeffs_X : d.mapCoeffs (X : A[X]) = 0 := by
  simp [← monomial_one_one_eq_X, PolynomialModule.single]

@[simp]
/-
**Derivation.mapCoeffs_C** 是 Mathlib 中的一个引理，位于命名空间 `Derivation`。
形式化陈述：mapCoeffs_C (x : A) : d.mapCoeffs (C x) = .single A 0 (d x)
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Derivation.mapCoeffs_monomial`：mapCoeffs_monomial (n : Nat) (x : A) : d.
mapCoeffs (monomial n x) = .single A n (d x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapCoeffs_C (x : A) :
    d.mapCoeffs (C x) = .single A 0 (d x) := by simp [← monomial_zero_left]

variable {B M' : Type*} [CommRing B] [Algebra R B] [Algebra A B]
    [AddCommGroup M'] [Module B M'] [Module R M'] [Module A M']
/-
**Derivation.apply_aeval_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：apply_aeval_eq' (d' : Derivation R B M') (f : M ->ₗ[A] M') (h : forall a, 
f (d a) = d' (algebraMap A B a)) (x : B) (p : A[X]) : d' (aeval x p) = Polynomia
lModule.eval x (PolynomialModule.map B f (d.mapCoeffs p)) + aeval x (derivative 
p) • d' x
参数：d' : Derivation R B M'；f : M ->ₗ[A] M'；h : forall a, f (d a) = d' (algebraMap
 A B a)；x : B；p : A[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `_private.Mathlib.RingTheory.Derivation.MapCoeffs.0.Derivation.apply_aeva
l_eq'._abel_1_1`：∀ {R : Type u_5} {A : Type u_4} {M : Type u_3} [inst : CommRing
 R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [inst_3 : AddCommGroup M] …
· 使用定理 `Polynomial.aeval_monomial`：aeval_monomial {n : Nat} {r : R} : aeval x (m
onomial n r) = algebraMap _ _ r * x ^ n
· 使用定理 `Derivation.leibniz`：leibniz : D (a * b) = a • D b + b • D a
· 使用定理 `Derivation.leibniz_pow`：leibniz_pow (n : Nat) : D (a ^ n) = n • a ^ (n -
 1) • D a
· 使用引理 `Derivation.mapCoeffs_monomial`：mapCoeffs_monomial (n : Nat) (x : A) : d.
mapCoeffs (monomial n x) = .single A n (d x)
· 使用定理 `PolynomialModule.map_single`：map_single (f : M ->ₗ[R] M') (i : Nat) (m :
 M) : map R' f (single R i m) = single R' i (f m)
· 使用定理 `PolynomialModule.eval_single`：eval_single (r : R) (i : Nat) (m : M) : ev
al r (single R i m) = r ^ i • m
· 使用定理 `Polynomial.derivative_monomial`：derivative_monomial (a : R) (n : Nat) : 
derivative (monomial n a) = monomial (n - 1) (a * n)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
-/
theorem apply_aeval_eq' (d' : Derivation R B M') (f : M →ₗ[A] M')
    (h : ∀ a, f (d a) = d' (algebraMap A B a)) (x : B) (p : A[X]) :
    d' (aeval x p) = PolynomialModule.eval x (PolynomialModule.map B f (d.mapCoeffs p)) +
      aeval x (derivative p) • d' x := by
  induction p using Polynomial.induction_on' with
  | add => simp_all only [map_add, add_smul]; abel
  | monomial =>
    simp only [aeval_monomial, leibniz, leibniz_pow, mapCoeffs_monomial,
      PolynomialModule.map_single, PolynomialModule.eval_single, derivative_monomial, map_mul,
      _root_.map_natCast, h]
    rw [add_comm, ← smul_smul, ← smul_smul, Nat.cast_smul_eq_nsmul]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Derivation.apply_aeval_eq** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：apply_aeval_eq [IsScalarTower R A B] [IsScalarTower A B M'] (d : Derivatio
n R B M') (x : B) (p : A[X]) : d (aeval x p) = (((d.compAlgebraMap A).mapCoeffs 
p).map B .id).eval x + aeval x (derivative p) • d x
参数：d : Derivation R B M'；x : B；p : A[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.apply_aeval_eq'`：apply_aeval_eq' (d' : Derivation R B M') (f 
: M ->ₗ[A] M') (h : forall a, f (d a) = d' (algebraMap A B a)) (x : B) (p : A[X]
) : d' (aeval x …
-/
theorem apply_aeval_eq [IsScalarTower R A B] [IsScalarTower A B M'] (d : Derivation R B M')
    (x : B) (p : A[X]) :
    d (aeval x p) =
      (((d.compAlgebraMap A).mapCoeffs p).map B .id).eval x + aeval x (derivative p) • d x :=
  apply_aeval_eq' (d.compAlgebraMap A) d LinearMap.id (fun _a ↦ rfl) x p
/-
**Derivation.apply_eval_eq** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：apply_eval_eq (x : A) (p : A[X]) : d (eval x p) = PolynomialModule.eval x 
(d.mapCoeffs p) + eval x (derivative p) • d x
参数：x : A；p : A[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PolynomialModule.ext`：∀ {R : Type u_2} {M : Type u_3} [inst : CommRing R
] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {x y : PolynomialModu
le R M}, x…
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Derivation.apply_aeval_eq`：apply_aeval_eq [IsScalarTower R A B] [IsScala
rTower A B M'] (d : Derivation R B M') (x : B) (p : A[X]) : d (aeval x p) = (((d
.compAlgebraMap…
-/
theorem apply_eval_eq (x : A) (p : A[X]) :
    d (eval x p) = PolynomialModule.eval x (d.mapCoeffs p) + eval x (derivative p) • d x := by
  convert! apply_aeval_eq d x p
  ext
  rfl

end Derivation

namespace Differential

variable {A : Type*} [CommRing A] [Differential A]

set_option backward.isDefEq.respectTransparency false in
/--
A specialization of `Derivation.mapCoeffs` for the case of a differential ring.
-/
/-
**Differential.mapCoeffs** 是 Mathlib 中的一个定义，位于命名空间 `Differential`。
形式化陈述：mapCoeffs : Derivation Int A[X] A[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A specialization of `Derivation.mapCoeffs` for the case of a differential ring.
-/
def mapCoeffs : Derivation ℤ A[X] A[X] :=
  PolynomialModule.equivPolynomialSelf.compDer Differential.deriv.mapCoeffs

@[simp]
/-
**Differential.coeff_mapCoeffs** 是 Mathlib 中的一个引理，位于命名空间 `Differential`。
形式化陈述：coeff_mapCoeffs (p : A[X]) (i) : coeff (mapCoeffs p) i = (coeff p i)′
参数：p : A[X]；i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeff_mapCoeffs (p : A[X]) (i) :
    coeff (mapCoeffs p) i = (coeff p i)′ := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Differential.mapCoeffs_monomial** 是 Mathlib 中的一个引理，位于命名空间 `Differential`。
形式化陈述：mapCoeffs_monomial (n : Nat) (x : A) : mapCoeffs (monomial n x) = monomial
 n x′
参数：n : Nat；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Derivation.mapCoeffs_monomial`：mapCoeffs_monomial (n : Nat) (x : A) : d.
mapCoeffs (monomial n x) = .single A n (d x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapCoeffs_monomial (n : ℕ) (x : A) :
    mapCoeffs (monomial n x) = monomial n x′ := by
  simp [mapCoeffs]

@[simp]
/-
**Differential.mapCoeffs_X** 是 Mathlib 中的一个引理，位于命名空间 `Differential`。
形式化陈述：mapCoeffs_X : mapCoeffs (X : A[X]) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Differential.mapCoeffs_monomial`：mapCoeffs_monomial (n : Nat) (x : A) : 
mapCoeffs (monomial n x) = monomial n x′
· 使用定理 `Derivation.map_one_eq_zero`：map_one_eq_zero : D 1 = 0
· 使用定理 `Polynomial.monomial_zero_right`：monomial_zero_right (n : Nat) : monomial
 n (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapCoeffs_X :
    mapCoeffs (X : A[X]) = 0 := by simp [← monomial_one_one_eq_X]

@[simp]
/-
**Differential.mapCoeffs_C** 是 Mathlib 中的一个引理，位于命名空间 `Differential`。
形式化陈述：mapCoeffs_C (x : A) : mapCoeffs (C x) = C x′
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Differential.mapCoeffs_monomial`：mapCoeffs_monomial (n : Nat) (x : A) : 
mapCoeffs (monomial n x) = monomial n x′
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapCoeffs_C (x : A) :
    mapCoeffs (C x) = C x′ := by simp [← monomial_zero_left]

variable {R : Type*} [CommRing R] [Differential R] [Algebra A R] [DifferentialAlgebra A R]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Differential.deriv_aeval_eq** 是 Mathlib 中的一个定理，位于命名空间 `Differential`。
形式化陈述：deriv_aeval_eq (x : R) (p : A[X]) : (aeval x p)′ = aeval x (mapCoeffs p) +
 aeval x (derivative p) * x′
参数：x : R；p : A[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PolynomialModule.aeval_equivPolynomial`：aeval_equivPolynomial {S : Type*
} [CommRing S] [Algebra S R] (f : PolynomialModule S S) (x : R) : aeval x (equiv
Polynomial f) = eval x (map …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Derivation.apply_aeval_eq'`：apply_aeval_eq' (d' : Derivation R B M') (f 
: M ->ₗ[A] M') (h : forall a, f (d a) = d' (algebraMap A B a)) (x : B) (p : A[X]
) : d' (aeval x …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `DifferentialAlgebra.deriv_algebraMap`：∀ {A : Type u_1} {B : Type u_2} {i
nst : CommRing A} {inst_1 : CommRing B} {inst_2 : Algebra A B}   {inst_3 : Diffe
rential A} {inst_4 : Diffe…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem deriv_aeval_eq (x : R) (p : A[X]) :
    (aeval x p)′ = aeval x (mapCoeffs p) + aeval x (derivative p) * x′ := by
  convert! Derivation.apply_aeval_eq' Differential.deriv _ (Algebra.linearMap A R) ..
  · simp [mapCoeffs]
  · simp [deriv_algebraMap]

/--
The unique derivation which can be made to a `DifferentialAlgebra` on `A[X]` with
`X′ = v`.
-/
/-
**Differential.implicitDeriv** 是 Mathlib 中的一个定义，位于命名空间 `Differential`。
形式化陈述：implicitDeriv (v : A[X]) : Derivation Int A[X] A[X]
参数：v : A[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique derivation which can be made to a `DifferentialAlgebra` on `A[X]` wit
h
`X′ = v`.
-/
def implicitDeriv (v : A[X]) :
    Derivation ℤ A[X] A[X] :=
  mapCoeffs + v • derivative'.restrictScalars ℤ

@[simp]
/-
**Differential.implicitDeriv_C** 是 Mathlib 中的一个引理，位于命名空间 `Differential`。
形式化陈述：implicitDeriv_C (v : A[X]) (b : A) : implicitDeriv v (C b) = C b′
参数：v : A[X]；b : A。
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
· 使用引理 `Differential.mapCoeffs_C`：mapCoeffs_C (x : A) : mapCoeffs (C x) = C x′
· 使用定理 `Polynomial.derivation_C`：derivation_C (D : Derivation R R[X] A) (a : R) 
: D (C a) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma implicitDeriv_C (v : A[X]) (b : A) :
    implicitDeriv v (C b) = C b′ := by
  simp [implicitDeriv]

@[simp]
/-
**Differential.implicitDeriv_X** 是 Mathlib 中的一个引理，位于命名空间 `Differential`。
形式化陈述：implicitDeriv_X (v : A[X]) : implicitDeriv v X = v
参数：v : A[X]。
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
· 使用引理 `Differential.mapCoeffs_X`：mapCoeffs_X : mapCoeffs (X : A[X]) = 0
· 使用定理 `Polynomial.derivative'_apply`：∀ {R : Type u_1} [inst : CommSemiring R] (
a : Polynomial R), Polynomial.derivative' a = Polynomial.derivative a
· 使用定理 `Polynomial.derivative_X`：derivative_X : derivative (X : R[X]) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma implicitDeriv_X (v : A[X]) :
    implicitDeriv v X = v := by
  simp [implicitDeriv]
/-
**Differential.deriv_aeval_eq_implicitDeriv** 是 Mathlib 中的一个引理，位于命名空间 `Different
ial`。
形式化陈述：deriv_aeval_eq_implicitDeriv (x : R) (v : A[X]) (h : x′ = aeval x v) (p : 
A[X]) : (aeval x p)′ = aeval x (implicitDeriv v p)
参数：x : R；v : A[X]；h : x′ = aeval x v；p : A[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Differential.deriv_aeval_eq`：deriv_aeval_eq (x : R) (p : A[X]) : (aeval 
x p)′ = aeval x (mapCoeffs p) + aeval x (derivative p) * x′
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.derivative'_apply`：∀ {R : Type u_1} [inst : CommSemiring R] (
a : Polynomial R), Polynomial.derivative' a = Polynomial.derivative a
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
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma deriv_aeval_eq_implicitDeriv (x : R) (v : A[X]) (h : x′ = aeval x v) (p : A[X]) :
    (aeval x p)′ = aeval x (implicitDeriv v p) := by
  simp [deriv_aeval_eq, implicitDeriv, h, mul_comm]

variable {R' : Type*} [CommRing R'] [Differential R'] [Algebra A R'] [DifferentialAlgebra A R']
variable [IsDomain R'] [Nontrivial R]
/-
**Differential.algHom_deriv** 是 Mathlib 中的一个引理，位于命名空间 `Differential`。
形式化陈述：algHom_deriv (f : R ->ₐ[A] R') (hf : Function.Injective f) (x : R) (h : Is
Separable A x) : f (x′) = (f x)′
参数：f : R ->ₐ[A] R'；hf : Function.Injective f；x : R；h : IsSeparable A x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_algHom`：aeval_algHom (f : A ->ₐ[R] B) (x : A) : aeval (
f x) = f.comp (aeval x)
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.Separable.aeval_derivative_ne_zero`：∀ {R : Type u} [inst : Co
mmSemiring R] {S : Type v} [inst_1 : CommSemiring S] [Nontrivial S] [inst_3 : Al
gebra R S]   {p : Polynomial R},   …
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `add_left_cancel`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] {a 
b c : G}, a + b = a + c → b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Differential.deriv_aeval_eq`：deriv_aeval_eq (x : R) (p : A[X]) : (aeval 
x p)′ = aeval x (mapCoeffs p) + aeval x (derivative p) * x′
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma algHom_deriv (f : R →ₐ[A] R') (hf : Function.Injective f) (x : R) (h : IsSeparable A x) :
    f (x′) = (f x)′ := by
  let p := minpoly A x
  apply mul_left_cancel₀ (a := aeval (f x) (derivative p))
  · rw [Polynomial.aeval_algHom]
    simp only [AlgHom.coe_comp, Function.comp_apply, ne_eq, map_eq_zero_iff f hf]
    apply Separable.aeval_derivative_ne_zero h (minpoly.aeval A x)
  conv => lhs; rw [Polynomial.aeval_algHom]
  simp only [AlgHom.coe_comp, Function.comp_apply, ← map_mul]
  apply add_left_cancel (a := aeval (f x) (mapCoeffs p))
  rw [← deriv_aeval_eq]
  simp only [aeval_algHom, AlgHom.coe_comp, Function.comp_apply, ← map_add, ← deriv_aeval_eq,
    minpoly.aeval, map_zero, p]

omit [Nontrivial R] in
/-
**Differential.algEquiv_deriv** 是 Mathlib 中的一个引理，位于命名空间 `Differential`。
形式化陈述：algEquiv_deriv (f : R ≃ₐ[A] R') (x : R) (h : IsSeparable A x) : f (x′) = (
f x)′
参数：f : R ≃ₐ[A] R'；x : R；h : IsSeparable A x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Differential.algHom_deriv`：algHom_deriv (f : R ->ₐ[A] R') (hf : Function
.Injective f) (x : R) (h : IsSeparable A x) : f (x′) = (f x)′
· 使用定理 `Equiv.nontrivial`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) [Nontrivia
l β], Nontrivial α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
-/
lemma algEquiv_deriv (f : R ≃ₐ[A] R') (x : R) (h : IsSeparable A x) :
    f (x′) = (f x)′ :=
  haveI := f.nontrivial
  algHom_deriv f.toAlgHom f.injective x h

variable [Algebra.IsSeparable A R]

/--
`algHom_deriv` in a separable algebra
-/
/-
**Differential.algHom_deriv'** 是 Mathlib 中的一个引理，位于命名空间 `Differential`。
形式化陈述：algHom_deriv' (f : R ->ₐ[A] R') (hf : Function.Injective f) (x : R) : f (x
′) = (f x)′
参数：f : R ->ₐ[A] R'；hf : Function.Injective f；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Differential.algHom_deriv`：algHom_deriv (f : R ->ₐ[A] R') (hf : Function
.Injective f) (x : R) (h : IsSeparable A x) : f (x′) = (f x)′
· 使用定理 `Algebra.IsSeparable.isSeparable'`：∀ {F : Type u_1} {K : Type u_3} {inst 
: CommRing F} {inst_1 : Ring K} {inst_2 : Algebra F K}   [self : Algebra.IsSepar
able F K] (x : K), IsS…

--- 原说明 ---
`algHom_deriv` in a separable algebra
-/
lemma algHom_deriv' (f : R →ₐ[A] R') (hf : Function.Injective f) (x : R) :
    f (x′) = (f x)′ := algHom_deriv f hf x (Algebra.IsSeparable.isSeparable' x)

omit [Nontrivial R] in
/--
`algEquiv_deriv` in a separable algebra
-/
/-
**Differential.algEquiv_deriv'** 是 Mathlib 中的一个引理，位于命名空间 `Differential`。
形式化陈述：algEquiv_deriv' (f : R ≃ₐ[A] R') (x : R) : f (x′) = (f x)′
参数：f : R ≃ₐ[A] R'；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Differential.algHom_deriv'`：algHom_deriv' (f : R ->ₐ[A] R') (hf : Functi
on.Injective f) (x : R) : f (x′) = (f x)′
· 使用定理 `Equiv.nontrivial`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) [Nontrivia
l β], Nontrivial α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …

--- 原说明 ---
`algEquiv_deriv` in a separable algebra
-/
lemma algEquiv_deriv' (f : R ≃ₐ[A] R') (x : R) :
    f (x′) = (f x)′ :=
  haveI := f.nontrivial
  algHom_deriv' f.toAlgHom f.injective x

end Differential

