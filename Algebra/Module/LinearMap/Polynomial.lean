/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Characteristic polynomials of linear families of endomorphisms

The coefficients of the characteristic polynomials of a linear family of endomorphisms
are homogeneous polynomials in the parameters.
This result is used in Lie theory
to establish the existence of regular elements and Cartan subalgebras,
and ultimately a well-defined notion of rank for Lie algebras.

In this file we prove this result about characteristic polynomials.
Let `L` and `M` be modules over a nontrivial commutative ring `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear map.
Let `b` be a basis of `L`, indexed by `ι`.
Then we define a multivariate polynomial with variables indexed by `ι`
that evaluates on elements `x` of `L` to the characteristic polynomial of `φ x`.

## Main declarations

* `Matrix.toMvPolynomial M i`: the family of multivariate polynomials that evaluates on `c : n → R`
  to the dot product of the `i`-th row of `M` with `c`.
  `Matrix.toMvPolynomial M i` is the sum of the monomials `C (M i j) * X j`.
* `LinearMap.toMvPolynomial b₁ b₂ f`: a version of `Matrix.toMvPolynomial` for linear maps `f`
  with respect to bases `b₁` and `b₂` of the domain and codomain.
* `LinearMap.polyCharpoly`: the multivariate polynomial that evaluates on elements `x` of `L`
  to the characteristic polynomial of `φ x`.
* `LinearMap.polyCharpoly_map_eq_charpoly`: the evaluation of `polyCharpoly` on elements `x` of `L`
  is the characteristic polynomial of `φ x`.
* `LinearMap.polyCharpoly_coeff_isHomogeneous`: the coefficients of `polyCharpoly`
  are homogeneous polynomials in the parameters.
* `LinearMap.nilRank`: the smallest index at which `polyCharpoly` has a non-zero coefficient,
  which is independent of the choice of basis for `L`.
* `LinearMap.IsNilRegular`: an element `x` of `L` is *nil-regular* with respect to `φ`
  if the `n`-th coefficient of the characteristic polynomial of `φ x` is non-zero,
  where `n` denotes the nil-rank of `φ`.

## Implementation details

We show that `LinearMap.polyCharpoly` does not depend on the choice of basis of the target module.
This is done via `LinearMap.polyCharpoly_eq_polyCharpolyAux`
and `LinearMap.polyCharpolyAux_basisIndep`.
The latter is proven by considering
the base change of the `R`-linear map `φ : L →ₗ[R] End R M`
to the multivariate polynomial ring `MvPolynomial ι R`,
and showing that `polyCharpolyAux φ` is equal to the characteristic polynomial of this base change.
The proof concludes because characteristic polynomials are independent of the chosen basis.

## References

* [barnes1967]: "On Cartan subalgebras of Lie algebras" by D.W. Barnes.

-/

@[expose] public section

open Module MvPolynomial
open scoped Matrix

namespace Matrix

variable {m n o R S : Type*}
variable [Fintype n] [Fintype o] [CommSemiring R] [CommSemiring S]

/-- Let `M` be an `(m × n)`-matrix over `R`.
Then `Matrix.toMvPolynomial M` is the family (indexed by `i : m`)
of multivariate polynomials in `n` variables over `R` that evaluates on `c : n → R`
to the dot product of the `i`-th row of `M` with `c`:
`Matrix.toMvPolynomial M i` is the sum of the monomials `C (M i j) * X j`. -/
noncomputable
/-
**Matrix.toMvPolynomial** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：toMvPolynomial (M : Matrix m n R) (i : m) : MvPolynomial n R
参数：M : Matrix m n R；i : m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toMvPolynomial (M : Matrix m n R) (i : m) : MvPolynomial n R :=
  ∑ j, monomial (.single j 1) (M i j)
/-
**Matrix.toMvPolynomial_eval_eq_apply** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：toMvPolynomial_eval_eq_apply (M : Matrix m n R) (i : m) (c : n -> R) : eva
l c (M.toMvPolynomial i) = (M *ᵥ c) i
参数：M : Matrix m n R；i : m；c : n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPolynomial.eval_monomial`：eval_monomial : eval f (monomial s a) = a * 
s.prod fun n e => f n ^ e
· 使用定理 `Finsupp.prod_single_index`：prod_single_index {a : α} {b : M} {h : α -> M
 -> N} (h_zero : h a 0 = 1) : (single a b).prod h = h a b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
lemma toMvPolynomial_eval_eq_apply (M : Matrix m n R) (i : m) (c : n → R) :
    eval c (M.toMvPolynomial i) = (M *ᵥ c) i := by
  simp only [toMvPolynomial, map_sum, eval_monomial, pow_zero, Finsupp.prod_single_index, pow_one,
    mulVec, dotProduct]
/-
**Matrix.toMvPolynomial_map** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：toMvPolynomial_map (f : R ->+* S) (M : Matrix m n R) (i : m) : (M.map f).t
oMvPolynomial i = MvPolynomial.map f (M.toMvPolynomial i)
参数：f : R ->+* S；M : Matrix m n R；i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPolynomial.map_monomial`：map_monomial (s : σ ->₀ Nat) (a : R) : map f 
(monomial s a) = monomial s (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toMvPolynomial_map (f : R →+* S) (M : Matrix m n R) (i : m) :
    (M.map f).toMvPolynomial i = MvPolynomial.map f (M.toMvPolynomial i) := by
  simp only [toMvPolynomial, map_apply, map_sum, map_monomial]
/-
**Matrix.toMvPolynomial_isHomogeneous** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：toMvPolynomial_isHomogeneous (M : Matrix m n R) (i : m) : (M.toMvPolynomia
l i).IsHomogeneous 1
参数：M : Matrix m n R；i : m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.IsHomogeneous.sum`：sum {ι : Type*} (s : Finset ι) (φ : ι ->
 MvPolynomial σ R) (n : Nat) (h : forall i in s, IsHomogeneous (φ i) n) : IsHomo
geneous (∑ i in s, φ…
· 使用定理 `MvPolynomial.isHomogeneous_monomial`：isHomogeneous_monomial {d : σ ->₀ N
at} (r : R) {n : Nat} (hn : d.degree = n) : IsHomogeneous (monomial d r) n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_single`：degree_single (a : σ) (r : R) : (Finsupp.single a
 r).degree = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toMvPolynomial_isHomogeneous (M : Matrix m n R) (i : m) :
    (M.toMvPolynomial i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  rintro j -
  apply MvPolynomial.isHomogeneous_monomial _ _
  simp
/-
**Matrix.toMvPolynomial_totalDegree_le** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：toMvPolynomial_totalDegree_le (M : Matrix m n R) (i : m) : (M.toMvPolynomi
al i).totalDegree <= 1
参数：M : Matrix m n R；i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPolynomial.IsHomogeneous.totalDegree_le`：totalDegree_le (hφ : IsHomoge
neous φ n) : φ.totalDegree <= n
· 使用引理 `Matrix.toMvPolynomial_isHomogeneous`：toMvPolynomial_isHomogeneous (M : M
atrix m n R) (i : m) : (M.toMvPolynomial i).IsHomogeneous 1
-/
lemma toMvPolynomial_totalDegree_le (M : Matrix m n R) (i : m) :
    (M.toMvPolynomial i).totalDegree ≤ 1 := by
  apply (toMvPolynomial_isHomogeneous _ _).totalDegree_le

@[simp]
/-
**Matrix.toMvPolynomial_constantCoeff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：toMvPolynomial_constantCoeff (M : Matrix m n R) (i : m) : constantCoeff (M
.toMvPolynomial i) = 0
参数：M : Matrix m n R；i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MvPolynomial.constantCoeff_X`：constantCoeff_X (i : σ) : constantCoeff (X
 i : MvPolynomial σ R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toMvPolynomial_constantCoeff (M : Matrix m n R) (i : m) :
    constantCoeff (M.toMvPolynomial i) = 0 := by
  simp only [toMvPolynomial, ← C_mul_X_eq_monomial, map_sum, map_mul, constantCoeff_X,
    mul_zero, Finset.sum_const_zero]

@[simp]
/-
**Matrix.toMvPolynomial_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：toMvPolynomial_zero : (0 : Matrix m n R).toMvPolynomial = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toMvPolynomial_zero : (0 : Matrix m n R).toMvPolynomial = 0 := by
  ext; simp only [toMvPolynomial, zero_apply, map_zero, Finset.sum_const_zero, Pi.zero_apply]

@[simp]
/-
**Matrix.toMvPolynomial_one** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：toMvPolynomial_one [DecidableEq n] : (1 : Matrix n n R).toMvPolynomial = X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toMvPolynomial.eq_1`：∀ {m : Type u_1} {n : Type u_2} {R : Type u_
4} [inst : Fintype n] [inst_1 : CommSemiring R] (M : Matrix m n R) (i : m),   M.
toMvPolynomial i…
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma toMvPolynomial_one [DecidableEq n] : (1 : Matrix n n R).toMvPolynomial = X := by
  ext i : 1
  rw [toMvPolynomial, Finset.sum_eq_single i]
  · simp only [one_apply_eq, ← C_mul_X_eq_monomial, C_1, one_mul]
  · rintro j - hj
    simp only [one_apply_ne hj.symm, map_zero]
  · grind
/-
**Matrix.toMvPolynomial_add** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：toMvPolynomial_add (M N : Matrix m n R) : (M + N).toMvPolynomial = M.toMvP
olynomial + N.toMvPolynomial
参数：M N : Matrix m n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toMvPolynomial_add (M N : Matrix m n R) :
    (M + N).toMvPolynomial = M.toMvPolynomial + N.toMvPolynomial := by
  ext i : 1
  simp only [toMvPolynomial, add_apply, map_add, Finset.sum_add_distrib, Pi.add_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Matrix.toMvPolynomial_mul** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：toMvPolynomial_mul (M : Matrix m n R) (N : Matrix n o R) (i : m) : (M * N)
.toMvPolynomial i = bind₁ N.toMvPolynomial (M.toMvPolynomial i)
参数：M : Matrix m n R；N : Matrix n o R；i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MvPolynomial.eval₂_monomial`：eval₂_monomial : (monomial s a).eval₂ f g =
 f a * s.prod fun n e => g n ^ e
· 使用定理 `Finsupp.prod_single_index`：prod_single_index {a : α} {b : M} {h : α -> M
 -> N} (h_zero : h a 0 = 1) : (single a b).prod h = h a b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `MvPolynomial.monomial_mul`：monomial_mul {s s' : σ ->₀ Nat} {a b : R} : m
onomial s a * monomial s' b = monomial (s + s') (a * b)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma toMvPolynomial_mul (M : Matrix m n R) (N : Matrix n o R) (i : m) :
    (M * N).toMvPolynomial i = bind₁ N.toMvPolynomial (M.toMvPolynomial i) := by
  simp only [toMvPolynomial, mul_apply, map_sum, Finset.sum_comm (γ := o), bind₁, aeval,
    AlgHom.coe_mk, coe_eval₂Hom, eval₂_monomial, algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, C_apply, pow_zero, Finsupp.prod_single_index, pow_one, Finset.mul_sum,
    monomial_mul, zero_add]

end Matrix

namespace LinearMap

open MvPolynomial

section

variable {R M₁ M₂ ι₁ ι₂ : Type*}
variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂]
variable [Module R M₁] [Module R M₂]
variable [Fintype ι₁] [Finite ι₂]
variable [DecidableEq ι₁]
variable (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂)

/-- Let `f : M₁ →ₗ[R] M₂` be an `R`-linear map
between modules `M₁` and `M₂` with bases `b₁` and `b₂` respectively.
Then `LinearMap.toMvPolynomial b₁ b₂ f` is the family of multivariate polynomials over `R`
that evaluates on an element `x` of `M₁` (represented on the basis `b₁`)
to the element `f x` of `M₂` (represented on the basis `b₂`). -/
noncomputable
/-
**LinearMap.toMvPolynomial** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：toMvPolynomial (f : M₁ ->ₗ[R] M₂) (i : ι₂) : MvPolynomial ι₁ R
参数：f : M₁ ->ₗ[R] M₂；i : ι₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toMvPolynomial (f : M₁ →ₗ[R] M₂) (i : ι₂) :
    MvPolynomial ι₁ R :=
  (toMatrix b₁ b₂ f).toMvPolynomial i
/-
**LinearMap.toMvPolynomial_eval_eq_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：toMvPolynomial_eval_eq_apply (f : M₁ ->ₗ[R] M₂) (i : ι₂) (c : ι₁ ->₀ R) : 
eval c (f.toMvPolynomial b₁ b₂ i) = b₂.repr (f (b₁.repr.symm c)) i
参数：f : M₁ ->ₗ[R] M₂；i : ι₂；c : ι₁ ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMvPolynomial.eq_1`：∀ {R : Type u_1} {M₁ : Type u_2} {M₂ : Ty
pe u_3} {ι₁ : Type u_4} {ι₂ : Type u_5} [inst : CommRing R]   [inst_1 : AddCommG
roup M₁] [inst_2 : …
· 使用引理 `Matrix.toMvPolynomial_eval_eq_apply`：toMvPolynomial_eval_eq_apply (M : M
atrix m n R) (i : m) (c : n -> R) : eval c (M.toMvPolynomial i) = (M *ᵥ c) i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.toMatrix_mulVec_repr`：LinearMap.toMatrix_mulVec_repr (f : M₁ -
>ₗ[R] M₂) (x : M₁) : LinearMap.toMatrix v₁ v₂ f *ᵥ v₁.repr x = v₂.repr (f x)
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
lemma toMvPolynomial_eval_eq_apply (f : M₁ →ₗ[R] M₂) (i : ι₂) (c : ι₁ →₀ R) :
    eval c (f.toMvPolynomial b₁ b₂ i) = b₂.repr (f (b₁.repr.symm c)) i := by
  rw [toMvPolynomial, Matrix.toMvPolynomial_eval_eq_apply,
    ← LinearMap.toMatrix_mulVec_repr b₁ b₂, LinearEquiv.apply_symm_apply]

open Algebra.TensorProduct in
/-
**LinearMap.toMvPolynomial_baseChange** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：toMvPolynomial_baseChange (f : M₁ ->ₗ[R] M₂) (i : ι₂) (A : Type*) [CommRin
g A] [Algebra R A] : (f.baseChange A).toMvPolynomial (basis A b₁) (basis A b₂) i
 = MvPolynomial.map (algebraMap R A) (f.toMvPolynomial b₁ b₂ i)
参数：f : M₁ ->ₗ[R] M₂；i : ι₂；A : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.toMatrix_baseChange`：toMatrix_baseChange (f : M₁ ->ₗ[R] M₂) (b
₁ : Basis ι R M₁) (b₂ : Basis ι₂ R M₂) : toMatrix (basis A b₁) (basis A b₂) (f.b
aseChange A) = (toM…
· 使用引理 `Matrix.toMvPolynomial_map`：toMvPolynomial_map (f : R ->+* S) (M : Matrix
 m n R) (i : m) : (M.map f).toMvPolynomial i = MvPolynomial.map f (M.toMvPolynom
ial i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toMvPolynomial_baseChange (f : M₁ →ₗ[R] M₂) (i : ι₂) (A : Type*) [CommRing A] [Algebra R A] :
    (f.baseChange A).toMvPolynomial (basis A b₁) (basis A b₂) i =
      MvPolynomial.map (algebraMap R A) (f.toMvPolynomial b₁ b₂ i) := by
  simp only [toMvPolynomial, toMatrix_baseChange, Matrix.toMvPolynomial_map]
/-
**LinearMap.toMvPolynomial_isHomogeneous** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：toMvPolynomial_isHomogeneous (f : M₁ ->ₗ[R] M₂) (i : ι₂) : (f.toMvPolynomi
al b₁ b₂ i).IsHomogeneous 1
参数：f : M₁ ->ₗ[R] M₂；i : ι₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.toMvPolynomial_isHomogeneous`：toMvPolynomial_isHomogeneous (M : M
atrix m n R) (i : m) : (M.toMvPolynomial i).IsHomogeneous 1
-/
lemma toMvPolynomial_isHomogeneous (f : M₁ →ₗ[R] M₂) (i : ι₂) :
    (f.toMvPolynomial b₁ b₂ i).IsHomogeneous 1 :=
  Matrix.toMvPolynomial_isHomogeneous _ _
/-
**LinearMap.toMvPolynomial_totalDegree_le** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：toMvPolynomial_totalDegree_le (f : M₁ ->ₗ[R] M₂) (i : ι₂) : (f.toMvPolynom
ial b₁ b₂ i).totalDegree <= 1
参数：f : M₁ ->ₗ[R] M₂；i : ι₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.toMvPolynomial_totalDegree_le`：toMvPolynomial_totalDegree_le (M :
 Matrix m n R) (i : m) : (M.toMvPolynomial i).totalDegree <= 1
-/
lemma toMvPolynomial_totalDegree_le (f : M₁ →ₗ[R] M₂) (i : ι₂) :
    (f.toMvPolynomial b₁ b₂ i).totalDegree ≤ 1 :=
  Matrix.toMvPolynomial_totalDegree_le _ _

@[simp]
/-
**LinearMap.toMvPolynomial_constantCoeff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：toMvPolynomial_constantCoeff (f : M₁ ->ₗ[R] M₂) (i : ι₂) : constantCoeff (
f.toMvPolynomial b₁ b₂ i) = 0
参数：f : M₁ ->ₗ[R] M₂；i : ι₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.toMvPolynomial_constantCoeff`：toMvPolynomial_constantCoeff (M : M
atrix m n R) (i : m) : constantCoeff (M.toMvPolynomial i) = 0
-/
lemma toMvPolynomial_constantCoeff (f : M₁ →ₗ[R] M₂) (i : ι₂) :
    constantCoeff (f.toMvPolynomial b₁ b₂ i) = 0 :=
  Matrix.toMvPolynomial_constantCoeff _ _

@[simp]
/-
**LinearMap.toMvPolynomial_zero** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：toMvPolynomial_zero : (0 : M₁ ->ₗ[R] M₂).toMvPolynomial b₁ b₂ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Matrix.toMvPolynomial_zero`：toMvPolynomial_zero : (0 : Matrix m n R).toM
vPolynomial = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toMvPolynomial_zero : (0 : M₁ →ₗ[R] M₂).toMvPolynomial b₁ b₂ = 0 := by
  unfold toMvPolynomial; simp only [map_zero, Matrix.toMvPolynomial_zero]

@[simp]
/-
**LinearMap.toMvPolynomial_id** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：toMvPolynomial_id : (id : M₁ ->ₗ[R] M₁).toMvPolynomial b₁ b₁ = X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.toMatrix_id`：LinearMap.toMatrix_id : LinearMap.toMatrix v₁ v₁ 
id = 1
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Matrix.toMvPolynomial_one`：toMvPolynomial_one [DecidableEq n] : (1 : Mat
rix n n R).toMvPolynomial = X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toMvPolynomial_id : (id : M₁ →ₗ[R] M₁).toMvPolynomial b₁ b₁ = X := by
  unfold toMvPolynomial; simp only [toMatrix_id, Matrix.toMvPolynomial_one]
/-
**LinearMap.toMvPolynomial_add** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：toMvPolynomial_add (f g : M₁ ->ₗ[R] M₂) : (f + g).toMvPolynomial b₁ b₂ = f
.toMvPolynomial b₁ b₂ + g.toMvPolynomial b₁ b₂
参数：f g : M₁ ->ₗ[R] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Matrix.toMvPolynomial_add`：toMvPolynomial_add (M N : Matrix m n R) : (M 
+ N).toMvPolynomial = M.toMvPolynomial + N.toMvPolynomial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toMvPolynomial_add (f g : M₁ →ₗ[R] M₂) :
    (f + g).toMvPolynomial b₁ b₂ = f.toMvPolynomial b₁ b₂ + g.toMvPolynomial b₁ b₂ := by
  unfold toMvPolynomial; simp only [map_add, Matrix.toMvPolynomial_add]

end

variable {R M₁ M₂ M₃ ι₁ ι₂ ι₃ : Type*}
variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M₁] [Module R M₂] [Module R M₃]
variable [Fintype ι₁] [Fintype ι₂] [Finite ι₃]
variable [DecidableEq ι₁] [DecidableEq ι₂]
variable (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂) (b₃ : Basis ι₃ R M₃)

/-
**LinearMap.toMvPolynomial_comp** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：toMvPolynomial_comp (g : M₂ ->ₗ[R] M₃) (f : M₁ ->ₗ[R] M₂) (i : ι₃) : (g ∘ₗ
 f).toMvPolynomial b₁ b₃ i = bind₁ (f.toMvPolynomial b₁ b₂) (g.toMvPolynomial b₂
 b₃ i)
参数：g : M₂ ->ₗ[R] M₃；f : M₁ ->ₗ[R] M₂；i : ι₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.toMatrix_comp`：LinearMap.toMatrix_comp [Finite l] [DecidableEq
 m] (f : M₂ ->ₗ[R] M₃) (g : M₁ ->ₗ[R] M₂) : LinearMap.toMatrix v₁ v₃ (f.comp g) 
= LinearMap.t…
· 使用引理 `Matrix.toMvPolynomial_mul`：toMvPolynomial_mul (M : Matrix m n R) (N : Ma
trix n o R) (i : m) : (M * N).toMvPolynomial i = bind₁ N.toMvPolynomial (M.toMvP
olynomial i)
-/
lemma toMvPolynomial_comp (g : M₂ →ₗ[R] M₃) (f : M₁ →ₗ[R] M₂) (i : ι₃) :
    (g ∘ₗ f).toMvPolynomial b₁ b₃ i =
      bind₁ (f.toMvPolynomial b₁ b₂) (g.toMvPolynomial b₂ b₃ i) := by
  simp only [toMvPolynomial, toMatrix_comp b₁ b₂ b₃, Matrix.toMvPolynomial_mul]
  rfl

end LinearMap

variable {R L M n ι ι' ιM : Type*}
variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
variable (φ : L →ₗ[R] Module.End R M)
variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

namespace LinearMap

section aux

variable [DecidableEq ιM] (b : Basis ι R L) (bₘ : Basis ιM R M)

open Matrix

/-- (Implementation detail, see `LinearMap.polyCharpoly`.)

Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear map.
Let `b` be a basis of `L` and `bₘ` a basis of `M`.
Then `LinearMap.polyCharpolyAux φ b bₘ` is the polynomial that evaluates on elements `x` of `L`
to the characteristic polynomial of `φ x` acting on `M`.

This definition does not depend on the choice of `bₘ`
(see `LinearMap.polyCharpolyAux_basisIndep`). -/
noncomputable
/-
**LinearMap.polyCharpolyAux** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：polyCharpolyAux : Polynomial (MvPolynomial ι R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def polyCharpolyAux : Polynomial (MvPolynomial ι R) :=
  (charpoly.univ R ιM).map <| MvPolynomial.bind₁ (φ.toMvPolynomial b bₘ.end)

set_option backward.defeqAttrib.useBackward true in
open Algebra.TensorProduct MvPolynomial in
/-
**LinearMap.polyCharpolyAux_baseChange** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：polyCharpolyAux_baseChange (A : Type*) [CommRing A] [Algebra R A] : polyCh
arpolyAux (tensorProduct _ _ _ _ ∘ₗ φ.baseChange A) (basis A b) (basis A bₘ) = (
polyCharpolyAux φ b bₘ).map (MvPolynomial.map (algebraMap R A))
参数：A : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.charpoly.univ_map_map`：univ_map_map : (univ R n).map (MvPolynomia
l.map f) = univ S n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `MvPolynomial.ringHom_ext`：ringHom_ext {A : Type*} [Semiring A] {f g : Mv
Polynomial σ R ->+* A} (hC : forall r, f (C r) = g (C r)) (hX : forall i, f (X i
) = g (X i)) :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用定理 `MvPolynomial.bind₁_C_right`：bind₁_C_right (f : σ -> MvPolynomial τ R) (x
) : bind₁ f (C x) = C x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `MvPolynomial.bind₁_X_right`：bind₁_X_right (f : σ -> MvPolynomial τ R) (i
 : σ) : bind₁ f (X i) = f i
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `LinearMap.toMvPolynomial_comp`：toMvPolynomial_comp (g : M₂ ->ₗ[R] M₃) (f
 : M₁ ->ₗ[R] M₂) (i : ι₃) : (g ∘ₗ f).toMvPolynomial b₁ b₃ i = bind₁ (f.toMvPolyn
omial b₁ b₂) (g.toM…
· 使用引理 `LinearMap.toMvPolynomial_baseChange`：toMvPolynomial_baseChange (f : M₁ -
>ₗ[R] M₂) (i : ι₂) (A : Type*) [CommRing A] [Algebra R A] : (f.baseChange A).toM
vPolynomial (basis A b₁) …
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `LinearMap.tensorProduct.eq_1`：∀ (R : Type u_1) (A : Type u_2) (M : Type 
u_3) (N : Type u_4) [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 
: Algebra R A] [in…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `TensorProduct.AlgebraTensorModule.lift_apply`：lift_apply (f : M ->ₗ[A] N
 ->ₗ[R] P) (a : M otimes[R] N) : AlgebraTensorModule.lift f a = TensorProduct.li
ft (LinearMap.restrictScalars R f)…
· 使用定理 `Algebra.TensorProduct.basis_apply`：basis_apply (i : ι) : basis A b i = 1
 otimesₜ b i
· 使用定理 `TensorProduct.lift.tmul`：∀ {R : Type u_1} {R₂ : Type u_2} [inst : CommSe
miring R] [inst_1 : CommSemiring R₂] {σ₁₂ : R →+* R₂} {M : Type u_7}   {N : Type
 u_8} {P₂ : T…
· 使用定理 `LinearMap.coe_restrictScalars`：coe_restrictScalars (f : M ->ₗ[S] M₂) : (
(f : M ->ₗ[R] M₂) : M -> M₂) = f
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Module.Basis.baseChange_end`：∀ {R : Type u_1} {M : Type uM} {ι : Type uι
} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] [inst_3 : Fin…
· 使用定理 `Module.Basis.repr_self_apply`：repr_self_apply (j) [Decidable (i = j)] : 
b.repr (b i) j = if i = j then 1 else 0
（共 38 条，此处仅展示前 30 条）
-/
lemma polyCharpolyAux_baseChange (A : Type*) [CommRing A] [Algebra R A] :
    polyCharpolyAux (tensorProduct _ _ _ _ ∘ₗ φ.baseChange A) (basis A b) (basis A bₘ) =
      (polyCharpolyAux φ b bₘ).map (MvPolynomial.map (algebraMap R A)) := by
  simp only [polyCharpolyAux]
  rw [← charpoly.univ_map_map _ (algebraMap R A)]
  simp only [Polynomial.map_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_C, bind₁_C_right]
  · rintro ij
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_X, bind₁_X_right]
    rw [toMvPolynomial_comp _ (basis A (Basis.end bₘ)), ← toMvPolynomial_baseChange]
    suffices toMvPolynomial (M₂ := (Module.End A (TensorProduct R A M)))
        (basis A bₘ.end) (basis A bₘ).end (tensorProduct R A M M) ij = X ij by
      rw [this, bind₁_X_right]
    simp only [toMvPolynomial, Matrix.toMvPolynomial]
    suffices ∀ kl,
        (toMatrix (basis A bₘ.end) (basis A bₘ).end) (tensorProduct R A M M) ij kl =
        if kl = ij then 1 else 0 by
      rw [Finset.sum_eq_single ij]
      · rw [this, if_pos rfl, X]
      · rintro kl - H
        rw [this, if_neg H, map_zero]
      · grind
    intro kl
    rw [toMatrix_apply, tensorProduct, TensorProduct.AlgebraTensorModule.lift_apply,
      basis_apply, TensorProduct.lift.tmul, coe_restrictScalars]
    dsimp only [coe_mk, AddHom.coe_mk, smul_apply, baseChangeHom_apply]
    rw [one_smul, Basis.baseChange_end, Basis.repr_self_apply]

open LinearMap in
/-
**LinearMap.polyCharpolyAux_map_eq_toMatrix_charpoly** 是 Mathlib 中的一个引理，位于命名空间 `
LinearMap`。
形式化陈述：polyCharpolyAux_map_eq_toMatrix_charpoly (x : L) : (polyCharpolyAux φ b bₘ
).map (MvPolynomial.eval (b.repr x)) = (toMatrix bₘ bₘ (φ x)).charpoly
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.polyCharpolyAux.eq_1`：∀ {R : Type u_1} {L : Type u_2} {M : Typ
e u_3} {ι : Type u_5} {ιM : Type u_7} [inst : CommRing R]   [inst_1 : AddCommGro
up L] [inst_2 : _roo…
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.eval₂Hom_C_eq_bind₁`：eval₂Hom_C_eq_bind₁ (f : σ -> MvPolyno
mial τ R) : eval₂Hom C f = bind₁ f
· 使用定理 `MvPolynomial.comp_eval₂Hom`：comp_eval₂Hom [CommSemiring S₂] (f : R ->+* 
S₁) (g : σ -> S₁) (φ : S₁ ->+* S₂) : φ.comp (eval₂Hom f g) = eval₂Hom (φ.comp f)
 fun i => φ (g i…
· 使用引理 `Matrix.charpoly.univ_map_eval₂Hom`：univ_map_eval₂Hom (M : n × n -> S) : 
(univ R n).map (eval₂Hom f M) = charpoly (Matrix.of M.curry)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Matrix.of_apply`：of_apply (f : m -> n -> α) (i j) : of f i j = f i j
· 使用定理 `Function.curry_apply`：∀ {α : Type u_1} {β : Type u_2} {γ : Sort u_3} (f 
: α × β → γ) (x : α) (y : β), Function.curry f x y = f (x, y)
· 使用引理 `LinearMap.toMvPolynomial_eval_eq_apply`：toMvPolynomial_eval_eq_apply (f 
: M₁ ->ₗ[R] M₂) (i : ι₂) (c : ι₁ ->₀ R) : eval c (f.toMvPolynomial b₁ b₂ i) = b₂
.repr (f (b₁.repr.symm c)) i
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
lemma polyCharpolyAux_map_eq_toMatrix_charpoly (x : L) :
    (polyCharpolyAux φ b bₘ).map (MvPolynomial.eval (b.repr x)) =
      (toMatrix bₘ bₘ (φ x)).charpoly := by
  rw [polyCharpolyAux, Polynomial.map_map, ← MvPolynomial.eval₂Hom_C_eq_bind₁,
    MvPolynomial.comp_eval₂Hom, charpoly.univ_map_eval₂Hom]
  congr
  ext
  rw [of_apply, Function.curry_apply, toMvPolynomial_eval_eq_apply, LinearEquiv.symm_apply_apply]
  rfl

open LinearMap in
/-
**LinearMap.polyCharpolyAux_eval_eq_toMatrix_charpoly_coeff** 是 Mathlib 中的一个引理，位
于命名空间 `LinearMap`。
形式化陈述：polyCharpolyAux_eval_eq_toMatrix_charpoly_coeff (x : L) (i : Nat) : MvPoly
nomial.eval (b.repr x) ((polyCharpolyAux φ b bₘ).coeff i) = (toMatrix bₘ bₘ (φ x
)).charpoly.coeff i
参数：x : L；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.polyCharpolyAux_map_eq_toMatrix_charpoly`：polyCharpolyAux_map_
eq_toMatrix_charpoly (x : L) : (polyCharpolyAux φ b bₘ).map (MvPolynomial.eval (
b.repr x)) = (toMatrix bₘ bₘ (φ x)).char…
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma polyCharpolyAux_eval_eq_toMatrix_charpoly_coeff (x : L) (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((polyCharpolyAux φ b bₘ).coeff i) =
      (toMatrix bₘ bₘ (φ x)).charpoly.coeff i := by
  simp [← polyCharpolyAux_map_eq_toMatrix_charpoly φ b bₘ x]

@[simp]
/-
**LinearMap.polyCharpolyAux_map_eq_charpoly** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap
`。
形式化陈述：polyCharpolyAux_map_eq_charpoly [Module.Finite R M] [Module.Free R M] (x :
 L) : (polyCharpolyAux φ b bₘ).map (MvPolynomial.eval (b.repr x)) = (φ x).charpo
ly
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.polyCharpolyAux_map_eq_toMatrix_charpoly`：polyCharpolyAux_map_
eq_toMatrix_charpoly (x : L) : (polyCharpolyAux φ b bₘ).map (MvPolynomial.eval (
b.repr x)) = (toMatrix bₘ bₘ (φ x)).char…
· 使用定理 `LinearMap.charpoly_toMatrix`：charpoly_toMatrix {ι : Type w} [DecidableEq
 ι] [Fintype ι] (b : Basis ι R M) : (toMatrix b b f).charpoly = f.charpoly
-/
lemma polyCharpolyAux_map_eq_charpoly [Module.Finite R M] [Module.Free R M]
    (x : L) :
    (polyCharpolyAux φ b bₘ).map (MvPolynomial.eval (b.repr x)) = (φ x).charpoly := by
  nontriviality R
  rw [polyCharpolyAux_map_eq_toMatrix_charpoly, LinearMap.charpoly_toMatrix]

@[simp]
/-
**LinearMap.polyCharpolyAux_coeff_eval** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：polyCharpolyAux_coeff_eval [Module.Finite R M] [Module.Free R M] (x : L) (
i : Nat) : MvPolynomial.eval (b.repr x) ((polyCharpolyAux φ b bₘ).coeff i) = (φ 
x).charpoly.coeff i
参数：x : L；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.polyCharpolyAux_map_eq_charpoly`：polyCharpolyAux_map_eq_charpo
ly [Module.Finite R M] [Module.Free R M] (x : L) : (polyCharpolyAux φ b bₘ).map 
(MvPolynomial.eval (b.repr x)) …
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
-/
lemma polyCharpolyAux_coeff_eval [Module.Finite R M] [Module.Free R M] (x : L) (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((polyCharpolyAux φ b bₘ).coeff i) = (φ x).charpoly.coeff i := by
  nontriviality R
  rw [← polyCharpolyAux_map_eq_charpoly φ b bₘ x, Polynomial.coeff_map]

set_option backward.isDefEq.respectTransparency.types false in
/-
**LinearMap.polyCharpolyAux_map_eval** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：polyCharpolyAux_map_eval [Module.Finite R M] [Module.Free R M] (x : ι -> R
) : (polyCharpolyAux φ b bₘ).map (MvPolynomial.eval x) = (φ (b.repr.symm (Finsup
p.equivFunOnFinite.symm x))).charpoly
参数：x : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.polyCharpolyAux_map_eq_charpoly`：polyCharpolyAux_map_eq_charpo
ly [Module.Finite R M] [Module.Free R M] (x : L) : (polyCharpolyAux φ b bₘ).map 
(MvPolynomial.eval (b.repr x)) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma polyCharpolyAux_map_eval [Module.Finite R M] [Module.Free R M]
    (x : ι → R) :
    (polyCharpolyAux φ b bₘ).map (MvPolynomial.eval x) =
      (φ (b.repr.symm (Finsupp.equivFunOnFinite.symm x))).charpoly := by
  simp only [← polyCharpolyAux_map_eq_charpoly φ b bₘ, LinearEquiv.apply_symm_apply,
    Finsupp.equivFunOnFinite, Equiv.coe_fn_symm_mk, Finsupp.coe_mk]

open Algebra.TensorProduct TensorProduct in
/-
**LinearMap.polyCharpolyAux_map_aeval** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：polyCharpolyAux_map_aeval (A : Type*) [CommRing A] [Algebra R A] [Module.F
inite A (A otimes[R] M)] [Module.Free A (A otimes[R] M)] (x : ι -> A) : (polyCha
rpolyAux φ b bₘ).map (MvPolynomial.aeval x).toRingHom = LinearMap.charpoly ((ten
sorProduct R A M M).comp (baseChange A φ) ((basis A b).repr.symm (Finsupp.equivF
unOnFinite.symm x)))
参数：A : Type*；A otimes[R] M；A otimes[R] M；x : ι -> A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.polyCharpolyAux_map_eval`：polyCharpolyAux_map_eval [Module.Fin
ite R M] [Module.Free R M] (x : ι -> R) : (polyCharpolyAux φ b bₘ).map (MvPolyno
mial.eval x) = (φ (b.rep…
· 使用引理 `LinearMap.polyCharpolyAux_baseChange`：polyCharpolyAux_baseChange (A : Ty
pe*) [CommRing A] [Algebra R A] : polyCharpolyAux (tensorProduct _ _ _ _ ∘ₗ φ.ba
seChange A) (basis A b) (b…
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `MvPolynomial.eval_map`：eval_map (f : R ->+* S₁) (g : σ -> S₁) (p : MvPol
ynomial σ R) : eval g (map f p) = eval₂ f g p
-/
lemma polyCharpolyAux_map_aeval
    (A : Type*) [CommRing A] [Algebra R A] [Module.Finite A (A ⊗[R] M)] [Module.Free A (A ⊗[R] M)]
    (x : ι → A) :
    (polyCharpolyAux φ b bₘ).map (MvPolynomial.aeval x).toRingHom =
      LinearMap.charpoly ((tensorProduct R A M M).comp (baseChange A φ)
        ((basis A b).repr.symm (Finsupp.equivFunOnFinite.symm x))) := by
  rw [← polyCharpolyAux_map_eval (tensorProduct R A M M ∘ₗ baseChange A φ) _ (basis A bₘ),
    polyCharpolyAux_baseChange, Polynomial.map_map]
  congr
  exact DFunLike.ext _ _ fun f ↦ (MvPolynomial.eval_map (algebraMap R A) x f).symm

open Algebra.TensorProduct MvPolynomial in
/-- `LinearMap.polyCharpolyAux` is independent of the choice of basis of the target module.

Proof strategy:
1. Rewrite `polyCharpolyAux` as the (honest, ordinary) characteristic polynomial
   of the base change of `φ` to the multivariate polynomial ring `MvPolynomial ι R`.
2. Use that the characteristic polynomial of a linear map is independent of the choice of basis.
   This independence result is used transitively via
   `LinearMap.polyCharpolyAux_map_aeval` and `LinearMap.polyCharpolyAux_map_eq_charpoly`.
-/
/-
**LinearMap.polyCharpolyAux_basisIndep** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：polyCharpolyAux_basisIndep {ιM' : Type*} [Fintype ιM'] [DecidableEq ιM'] (
bₘ' : Basis ιM' R M) : polyCharpolyAux φ b bₘ = polyCharpolyAux φ b bₘ'
参数：bₘ' : Basis ιM' R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aeval_X_left`：aeval_X_left : aeval X = AlgHom.id R (MvPolyn
omial σ R)
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `LinearMap.polyCharpolyAux_map_aeval`：polyCharpolyAux_map_aeval (A : Type
*) [CommRing A] [Algebra R A] [Module.Finite A (A otimes[R] M)] [Module.Free A (
A otimes[R] M)] (x : ι ->…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`LinearMap.polyCharpolyAux` is independent of the choice of basis of the target 
module.

Proof strategy:
1. Rewrite `polyCharpolyAux` as the (honest, ordinary) characteristic polynomial
   of the base change of `φ` to the multivariate polynomial ring `MvPolynomial ι
 R`.
2. Use that the characteristic polynomial of a linear map is independent of the 
choice of basis.
   This independence result is used transitively via
   `LinearMap.polyCharpolyAux_map_aeval` and `LinearMap.polyCharpolyAux_map_eq_c
harpoly`.
-/
lemma polyCharpolyAux_basisIndep {ιM' : Type*} [Fintype ιM'] [DecidableEq ιM']
    (bₘ' : Basis ιM' R M) :
    polyCharpolyAux φ b bₘ = polyCharpolyAux φ b bₘ' := by
  let f : Polynomial (MvPolynomial ι R) → Polynomial (MvPolynomial ι R) :=
    Polynomial.map (MvPolynomial.aeval X).toRingHom
  have hf : Function.Injective f := by
    simp only [f, aeval_X_left, AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom]
    exact Polynomial.map_injective (RingHom.id _) Function.injective_id
  apply hf
  let _h1 : Module.Finite (MvPolynomial ι R) (TensorProduct R (MvPolynomial ι R) M) :=
    Module.Finite.of_basis (basis (MvPolynomial ι R) bₘ)
  let _h2 : Module.Free (MvPolynomial ι R) (TensorProduct R (MvPolynomial ι R) M) :=
    Module.Free.of_basis (basis (MvPolynomial ι R) bₘ)
  simp only [f, polyCharpolyAux_map_aeval, polyCharpolyAux_map_aeval]

end aux

open Module Matrix

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

/-- Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear family of endomorphisms.
Let `b` be a basis of `L` and `bₘ` a basis of `M`.
Then `LinearMap.polyCharpoly φ b` is the polynomial that evaluates on elements `x` of `L`
to the characteristic polynomial of `φ x` acting on `M`. -/
noncomputable
/-
**LinearMap.polyCharpoly** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：polyCharpoly : Polynomial (MvPolynomial ι R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def polyCharpoly : Polynomial (MvPolynomial ι R) :=
  φ.polyCharpolyAux b (Module.Free.chooseBasis R M)
/-
**LinearMap.polyCharpoly_eq_of_basis** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：polyCharpoly_eq_of_basis [DecidableEq ιM] (bₘ : Basis ιM R M) : polyCharpo
ly φ b = (charpoly.univ R ιM).map (MvPolynomial.bind₁ (φ.toMvPolynomial b bₘ.end
))
参数：bₘ : Basis ιM R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.polyCharpoly.eq_1`：∀ {R : Type u_1} {L : Type u_2} {M : Type u
_3} {ι : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup L]   [inst_2 : _ro
ot_.Module R L] […
· 使用引理 `LinearMap.polyCharpolyAux_basisIndep`：polyCharpolyAux_basisIndep {ιM' : 
Type*} [Fintype ιM'] [DecidableEq ιM'] (bₘ' : Basis ιM' R M) : polyCharpolyAux φ
 b bₘ = polyCharpolyAux φ …
· 使用定理 `LinearMap.polyCharpolyAux.eq_1`：∀ {R : Type u_1} {L : Type u_2} {M : Typ
e u_3} {ι : Type u_5} {ιM : Type u_7} [inst : CommRing R]   [inst_1 : AddCommGro
up L] [inst_2 : _roo…
-/
lemma polyCharpoly_eq_of_basis [DecidableEq ιM] (bₘ : Basis ιM R M) :
    polyCharpoly φ b =
    (charpoly.univ R ιM).map (MvPolynomial.bind₁ (φ.toMvPolynomial b bₘ.end)) := by
  rw [polyCharpoly, φ.polyCharpolyAux_basisIndep b (Module.Free.chooseBasis R M) bₘ,
    polyCharpolyAux]
/-
**LinearMap.polyCharpoly_monic** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：polyCharpoly_monic : (polyCharpoly φ b).Monic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用引理 `Matrix.charpoly.univ_monic`：univ_monic : (univ R n).Monic
-/
lemma polyCharpoly_monic : (polyCharpoly φ b).Monic :=
  (charpoly.univ_monic R _).map _
/-
**LinearMap.polyCharpoly_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：polyCharpoly_ne_zero [Nontrivial R] : (polyCharpoly φ b) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用引理 `LinearMap.polyCharpoly_monic`：polyCharpoly_monic : (polyCharpoly φ b).Mo
nic
-/
lemma polyCharpoly_ne_zero [Nontrivial R] : (polyCharpoly φ b) ≠ 0 :=
  (polyCharpoly_monic _ _).ne_zero

@[simp]
/-
**LinearMap.polyCharpoly_natDegree** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：polyCharpoly_natDegree [Nontrivial R] : (polyCharpoly φ b).natDegree = fin
rank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.polyCharpoly.eq_1`：∀ {R : Type u_1} {L : Type u_2} {M : Type u
_3} {ι : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup L]   [inst_2 : _ro
ot_.Module R L] […
· 使用定理 `LinearMap.polyCharpolyAux.eq_1`：∀ {R : Type u_1} {L : Type u_2} {M : Typ
e u_3} {ι : Type u_5} {ιM : Type u_7} [inst : CommRing R]   [inst_1 : AddCommGro
up L] [inst_2 : _roo…
· 使用定理 `Polynomial.Monic.natDegree_map`：∀ {R : Type u} {S : Type v} [inst : Semi
ring R] [inst_1 : Semiring S] [Nontrivial S] {P : Polynomial R},   P.Monic → ∀ (
f : R →+* S), (Polyn…
· 使用引理 `Matrix.charpoly.univ_monic`：univ_monic : (univ R n).Monic
· 使用引理 `Matrix.charpoly.univ_natDegree`：univ_natDegree [Nontrivial R] : (univ R 
n).natDegree = Fintype.card n
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
-/
lemma polyCharpoly_natDegree [Nontrivial R] :
    (polyCharpoly φ b).natDegree = finrank R M := by
  rw [polyCharpoly, polyCharpolyAux, (charpoly.univ_monic _ _).natDegree_map,
    charpoly.univ_natDegree, finrank_eq_card_chooseBasisIndex]
/-
**LinearMap.polyCharpoly_coeff_isHomogeneous** 是 Mathlib 中的一个引理，位于命名空间 `LinearMa
p`。
形式化陈述：polyCharpoly_coeff_isHomogeneous (i j : Nat) (hij : i + j = finrank R M) [
Nontrivial R] : ((polyCharpoly φ b).coeff i).IsHomogeneous j
参数：i j : Nat；hij : i + j = finrank R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.polyCharpoly.eq_1`：∀ {R : Type u_1} {L : Type u_2} {M : Type u
_3} {ι : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup L]   [inst_2 : _ro
ot_.Module R L] […
· 使用定理 `LinearMap.polyCharpolyAux.eq_1`：∀ {R : Type u_1} {L : Type u_2} {M : Typ
e u_3} {ι : Type u_5} {ιM : Type u_7} [inst : CommRing R]   [inst_1 : AddCommGro
up L] [inst_2 : _roo…
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `MvPolynomial.IsHomogeneous.eval₂`：eval₂ (hφ : φ.IsHomogeneous m) (f : R 
->+* MvPolynomial τ S) (g : σ -> MvPolynomial τ S) (hf : forall r, (f r).IsHomog
eneous 0) (hg : forall…
· 使用引理 `Matrix.charpoly.univ_coeff_isHomogeneous`：univ_coeff_isHomogeneous (i j 
: Nat) (h : i + j = Fintype.card n) : ((univ R n).coeff i).IsHomogeneous j
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `MvPolynomial.isHomogeneous_C`：isHomogeneous_C (r : R) : IsHomogeneous (C
 r : MvPolynomial σ R) 0
· 使用引理 `LinearMap.toMvPolynomial_isHomogeneous`：toMvPolynomial_isHomogeneous (f 
: M₁ ->ₗ[R] M₂) (i : ι₂) : (f.toMvPolynomial b₁ b₂ i).IsHomogeneous 1
-/
lemma polyCharpoly_coeff_isHomogeneous (i j : ℕ) (hij : i + j = finrank R M) [Nontrivial R] :
    ((polyCharpoly φ b).coeff i).IsHomogeneous j := by
  rw [finrank_eq_card_chooseBasisIndex] at hij
  rw [polyCharpoly, polyCharpolyAux, Polynomial.coeff_map, ← one_mul j]
  apply (charpoly.univ_coeff_isHomogeneous _ _ _ _ hij).eval₂
  · exact fun r ↦ MvPolynomial.isHomogeneous_C _ _
  · exact LinearMap.toMvPolynomial_isHomogeneous _ _ _

open Algebra.TensorProduct MvPolynomial in
/-
**LinearMap.polyCharpoly_baseChange** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：polyCharpoly_baseChange (A : Type*) [CommRing A] [Algebra R A] : polyCharp
oly (tensorProduct _ _ _ _ ∘ₗ φ.baseChange A) (basis A b) = (polyCharpoly φ b).m
ap (MvPolynomial.map (algebraMap R A))
参数：A : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.polyCharpolyAux_baseChange`：polyCharpolyAux_baseChange (A : Ty
pe*) [CommRing A] [Algebra R A] : polyCharpolyAux (tensorProduct _ _ _ _ ∘ₗ φ.ba
seChange A) (basis A b) (b…
· 使用引理 `LinearMap.polyCharpolyAux_basisIndep`：polyCharpolyAux_basisIndep {ιM' : 
Type*} [Fintype ιM'] [DecidableEq ιM'] (bₘ' : Basis ιM' R M) : polyCharpolyAux φ
 b bₘ = polyCharpolyAux φ …
-/
lemma polyCharpoly_baseChange (A : Type*) [CommRing A] [Algebra R A] :
    polyCharpoly (tensorProduct _ _ _ _ ∘ₗ φ.baseChange A) (basis A b) =
      (polyCharpoly φ b).map (MvPolynomial.map (algebraMap R A)) := by
  unfold polyCharpoly
  rw [← φ.polyCharpolyAux_baseChange]
  apply polyCharpolyAux_basisIndep

@[simp]
/-
**LinearMap.polyCharpoly_map_eq_charpoly** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：polyCharpoly_map_eq_charpoly (x : L) : (polyCharpoly φ b).map (MvPolynomia
l.eval (b.repr x)) = (φ x).charpoly
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.polyCharpoly.eq_1`：∀ {R : Type u_1} {L : Type u_2} {M : Type u
_3} {ι : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup L]   [inst_2 : _ro
ot_.Module R L] […
· 使用引理 `LinearMap.polyCharpolyAux_map_eq_charpoly`：polyCharpolyAux_map_eq_charpo
ly [Module.Finite R M] [Module.Free R M] (x : L) : (polyCharpolyAux φ b bₘ).map 
(MvPolynomial.eval (b.repr x)) …
-/
lemma polyCharpoly_map_eq_charpoly (x : L) :
    (polyCharpoly φ b).map (MvPolynomial.eval (b.repr x)) = (φ x).charpoly := by
  rw [polyCharpoly, polyCharpolyAux_map_eq_charpoly]

@[simp]
/-
**LinearMap.polyCharpoly_coeff_eval** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：polyCharpoly_coeff_eval (x : L) (i : Nat) : MvPolynomial.eval (b.repr x) (
(polyCharpoly φ b).coeff i) = (φ x).charpoly.coeff i
参数：x : L；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.polyCharpoly.eq_1`：∀ {R : Type u_1} {L : Type u_2} {M : Type u
_3} {ι : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup L]   [inst_2 : _ro
ot_.Module R L] […
· 使用引理 `LinearMap.polyCharpolyAux_coeff_eval`：polyCharpolyAux_coeff_eval [Module
.Finite R M] [Module.Free R M] (x : L) (i : Nat) : MvPolynomial.eval (b.repr x) 
((polyCharpolyAux φ b bₘ).…
-/
lemma polyCharpoly_coeff_eval (x : L) (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((polyCharpoly φ b).coeff i) = (φ x).charpoly.coeff i := by
  rw [polyCharpoly, polyCharpolyAux_coeff_eval]
/-
**LinearMap.polyCharpoly_coeff_eq_zero_of_basis** 是 Mathlib 中的一个引理，位于命名空间 `Linea
rMap`。
形式化陈述：polyCharpoly_coeff_eq_zero_of_basis (b : Basis ι R L) (b' : Basis ι' R L) 
(k : Nat) (H : (polyCharpoly φ b).coeff k = 0) : (polyCharpoly φ b').coeff k = 0
参数：b : Basis ι R L；b' : Basis ι' R L；k : Nat；H : (polyCharpoly φ b).coeff k = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.polyCharpoly.eq_1`：∀ {R : Type u_1} {L : Type u_2} {M : Type u
_3} {ι : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup L]   [inst_2 : _ro
ot_.Module R L] […
· 使用定理 `LinearMap.polyCharpolyAux.eq_1`：∀ {R : Type u_1} {L : Type u_2} {M : Typ
e u_3} {ι : Type u_5} {ιM : Type u_7} [inst : CommRing R]   [inst_1 : AddCommGro
up L] [inst_2 : _roo…
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `LinearMap.toMvPolynomial_comp`：toMvPolynomial_comp (g : M₂ ->ₗ[R] M₃) (f
 : M₁ ->ₗ[R] M₂) (i : ι₃) : (g ∘ₗ f).toMvPolynomial b₁ b₃ i = bind₁ (f.toMvPolyn
omial b₁ b₂) (g.toM…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.bind₁_bind₁`：bind₁_bind₁ {υ : Type*} (f : σ -> MvPolynomial
 τ R) (g : τ -> MvPolynomial υ R) (φ : MvPolynomial σ R) : (bind₁ g) (bind₁ f φ)
 = bind₁ (fun …
· 使用定理 `RingHom.coe_coe`：coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β
] (f : F) : ((f : α ->+* β) : α -> β) = f
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma polyCharpoly_coeff_eq_zero_of_basis (b : Basis ι R L) (b' : Basis ι' R L) (k : ℕ)
    (H : (polyCharpoly φ b).coeff k = 0) :
    (polyCharpoly φ b').coeff k = 0 := by
  rw [polyCharpoly, polyCharpolyAux, Polynomial.coeff_map] at H ⊢
  set B := (Module.Free.chooseBasis R M).end
  set g := toMvPolynomial b' b LinearMap.id
  apply_fun (MvPolynomial.bind₁ g) at H
  have : toMvPolynomial b' B φ = fun i ↦ (MvPolynomial.bind₁ g) (toMvPolynomial b B φ i) :=
    funext <| toMvPolynomial_comp b' b B φ LinearMap.id
  rwa [map_zero, RingHom.coe_coe, MvPolynomial.bind₁_bind₁, ← this] at H
/-
**LinearMap.polyCharpoly_coeff_eq_zero_iff_of_basis** 是 Mathlib 中的一个引理，位于命名空间 `L
inearMap`。
形式化陈述：polyCharpoly_coeff_eq_zero_iff_of_basis (b : Basis ι R L) (b' : Basis ι' R
 L) (k : Nat) : (polyCharpoly φ b).coeff k = 0 ↔ (polyCharpoly φ b').coeff k = 0
参数：b : Basis ι R L；b' : Basis ι' R L；k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.polyCharpoly_coeff_eq_zero_of_basis`：polyCharpoly_coeff_eq_zer
o_of_basis (b : Basis ι R L) (b' : Basis ι' R L) (k : Nat) (H : (polyCharpoly φ 
b).coeff k = 0) : (polyCharpoly φ b…
-/
lemma polyCharpoly_coeff_eq_zero_iff_of_basis (b : Basis ι R L) (b' : Basis ι' R L) (k : ℕ) :
    (polyCharpoly φ b).coeff k = 0 ↔ (polyCharpoly φ b').coeff k = 0 := by
  constructor <;> apply polyCharpoly_coeff_eq_zero_of_basis

section aux

/-- (Implementation detail, see `LinearMap.nilRank`.)

Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear family of endomorphisms.
Then `LinearMap.nilRankAux φ b` is the smallest index
at which `LinearMap.polyCharpoly φ b` has a non-zero coefficient.

This number does not depend on the choice of `b`, see `nilRankAux_basis_indep`. -/
noncomputable
/-
**LinearMap.nilRankAux** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：nilRankAux (φ : L ->ₗ[R] Module.End R M) (b : Basis ι R L) : Nat
参数：φ : L ->ₗ[R] Module.End R M；b : Basis ι R L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def nilRankAux (φ : L →ₗ[R] Module.End R M) (b : Basis ι R L) : ℕ :=
  (polyCharpoly φ b).natTrailingDegree
/-
**LinearMap.polyCharpoly_coeff_nilRankAux_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Lin
earMap`。
形式化陈述：polyCharpoly_coeff_nilRankAux_ne_zero [Nontrivial R] : (polyCharpoly φ b).
coeff (nilRankAux φ b) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.trailingCoeff_nonzero_iff_nonzero`：trailingCoeff_nonzero_iff_
nonzero : trailingCoeff p != 0 ↔ p != 0
· 使用引理 `LinearMap.polyCharpoly_ne_zero`：polyCharpoly_ne_zero [Nontrivial R] : (p
olyCharpoly φ b) != 0
-/
lemma polyCharpoly_coeff_nilRankAux_ne_zero [Nontrivial R] :
    (polyCharpoly φ b).coeff (nilRankAux φ b) ≠ 0 := by
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
  apply polyCharpoly_ne_zero
/-
**LinearMap.nilRankAux_le** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：nilRankAux_le [Nontrivial R] (b : Basis ι R L) (b' : Basis ι' R L) : nilRa
nkAux φ b <= nilRankAux φ b'
参数：b : Basis ι R L；b' : Basis ι' R L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natTrailingDegree_le_of_ne_zero`：natTrailingDegree_le_of_ne_z
ero (h : coeff p n != 0) : natTrailingDegree p <= n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `LinearMap.polyCharpoly_coeff_eq_zero_iff_of_basis`：polyCharpoly_coeff_eq
_zero_iff_of_basis (b : Basis ι R L) (b' : Basis ι' R L) (k : Nat) : (polyCharpo
ly φ b).coeff k = 0 ↔ (polyCharpoly φ b…
· 使用引理 `LinearMap.polyCharpoly_coeff_nilRankAux_ne_zero`：polyCharpoly_coeff_nilR
ankAux_ne_zero [Nontrivial R] : (polyCharpoly φ b).coeff (nilRankAux φ b) != 0
-/
lemma nilRankAux_le [Nontrivial R] (b : Basis ι R L) (b' : Basis ι' R L) :
    nilRankAux φ b ≤ nilRankAux φ b' := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  rw [Ne, (polyCharpoly_coeff_eq_zero_iff_of_basis φ b b' _).not]
  apply polyCharpoly_coeff_nilRankAux_ne_zero
/-
**LinearMap.nilRankAux_basis_indep** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：nilRankAux_basis_indep [Nontrivial R] (b : Basis ι R L) (b' : Basis ι' R L
) : nilRankAux φ b = (polyCharpoly φ b').natTrailingDegree
参数：b : Basis ι R L；b' : Basis ι' R L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `LinearMap.nilRankAux_le`：nilRankAux_le [Nontrivial R] (b : Basis ι R L) 
(b' : Basis ι' R L) : nilRankAux φ b <= nilRankAux φ b'
-/
lemma nilRankAux_basis_indep [Nontrivial R] (b : Basis ι R L) (b' : Basis ι' R L) :
    nilRankAux φ b = (polyCharpoly φ b').natTrailingDegree := by
  apply le_antisymm <;> apply nilRankAux_le

end aux

variable [Module.Finite R L] [Module.Free R L]

/-- Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear family of endomorphisms.
Then `LinearMap.nilRank φ b` is the smallest index
at which `LinearMap.polyCharpoly φ b` has a non-zero coefficient.

This number does not depend on the choice of `b`,
see `LinearMap.nilRank_eq_polyCharpoly_natTrailingDegree`. -/
noncomputable
/-
**LinearMap.nilRank** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：nilRank (φ : L ->ₗ[R] Module.End R M) : Nat
参数：φ : L ->ₗ[R] Module.End R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def nilRank (φ : L →ₗ[R] Module.End R M) : ℕ :=
  nilRankAux φ (Module.Free.chooseBasis R L)

section
variable [Nontrivial R]

/-
**LinearMap.nilRank_eq_polyCharpoly_natTrailingDegree** 是 Mathlib 中的一个引理，位于命名空间 
`LinearMap`。
形式化陈述：nilRank_eq_polyCharpoly_natTrailingDegree (b : Basis ι R L) : nilRank φ = 
(polyCharpoly φ b).natTrailingDegree
参数：b : Basis ι R L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.nilRankAux_basis_indep`：nilRankAux_basis_indep [Nontrivial R] 
(b : Basis ι R L) (b' : Basis ι' R L) : nilRankAux φ b = (polyCharpoly φ b').nat
TrailingDegree
-/
lemma nilRank_eq_polyCharpoly_natTrailingDegree (b : Basis ι R L) :
    nilRank φ = (polyCharpoly φ b).natTrailingDegree := by
  apply nilRankAux_basis_indep
/-
**LinearMap.polyCharpoly_coeff_nilRank_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Linear
Map`。
形式化陈述：polyCharpoly_coeff_nilRank_ne_zero : (polyCharpoly φ b).coeff (nilRank φ) 
!= 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.nilRank_eq_polyCharpoly_natTrailingDegree`：nilRank_eq_polyChar
poly_natTrailingDegree (b : Basis ι R L) : nilRank φ = (polyCharpoly φ b).natTra
ilingDegree
· 使用引理 `LinearMap.polyCharpoly_coeff_nilRankAux_ne_zero`：polyCharpoly_coeff_nilR
ankAux_ne_zero [Nontrivial R] : (polyCharpoly φ b).coeff (nilRankAux φ b) != 0
-/
lemma polyCharpoly_coeff_nilRank_ne_zero :
    (polyCharpoly φ b).coeff (nilRank φ) ≠ 0 := by
  rw [nilRank_eq_polyCharpoly_natTrailingDegree _ b]
  apply polyCharpoly_coeff_nilRankAux_ne_zero

open Module Module.Free
/-
**LinearMap.nilRank_le_card** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：nilRank_le_card {ι : Type*} [Fintype ι] (b : Basis ι R M) : nilRank φ <= F
intype.card ι
参数：b : Basis ι R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natTrailingDegree_le_of_ne_zero`：natTrailingDegree_le_of_ne_z
ero (h : coeff p n != 0) : natTrailingDegree p <= n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用引理 `LinearMap.polyCharpoly_natDegree`：polyCharpoly_natDegree [Nontrivial R] 
: (polyCharpoly φ b).natDegree = finrank R M
· 使用定理 `Polynomial.coeff_natDegree`：coeff_natDegree : coeff p (natDegree p) = le
adingCoeff p
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用引理 `LinearMap.polyCharpoly_monic`：polyCharpoly_monic : (polyCharpoly φ b).Mo
nic
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
lemma nilRank_le_card {ι : Type*} [Fintype ι] (b : Basis ι R M) : nilRank φ ≤ Fintype.card ι := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  rw [← Module.finrank_eq_card_basis b, ← polyCharpoly_natDegree φ (chooseBasis R L),
    Polynomial.coeff_natDegree, (polyCharpoly_monic _ _).leadingCoeff]
  apply one_ne_zero
/-
**LinearMap.nilRank_le_finrank** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：nilRank_le_finrank : nilRank φ <= finrank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用引理 `LinearMap.nilRank_le_card`：nilRank_le_card {ι : Type*} [Fintype ι] (b : 
Basis ι R M) : nilRank φ <= Fintype.card ι
-/
lemma nilRank_le_finrank : nilRank φ ≤ finrank R M := by
  simpa only [finrank_eq_card_chooseBasisIndex R M] using nilRank_le_card φ (chooseBasis R M)
/-
**LinearMap.nilRank_le_natTrailingDegree_charpoly** 是 Mathlib 中的一个引理，位于命名空间 `Lin
earMap`。
形式化陈述：nilRank_le_natTrailingDegree_charpoly (x : L) : nilRank φ <= (φ x).charpol
y.natTrailingDegree
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natTrailingDegree_le_of_ne_zero`：natTrailingDegree_le_of_ne_z
ero (h : coeff p n != 0) : natTrailingDegree p <= n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.trailingCoeff_nonzero_iff_nonzero`：trailingCoeff_nonzero_iff_
nonzero : trailingCoeff p != 0 ↔ p != 0
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `LinearMap.charpoly_monic`：charpoly_monic : f.charpoly.Monic
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
· 使用引理 `LinearMap.polyCharpoly_coeff_eval`：polyCharpoly_coeff_eval (x : L) (i : 
Nat) : MvPolynomial.eval (b.repr x) ((polyCharpoly φ b).coeff i) = (φ x).charpol
y.coeff i
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma nilRank_le_natTrailingDegree_charpoly (x : L) :
    nilRank φ ≤ (φ x).charpoly.natTrailingDegree := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  intro h
  apply_fun (MvPolynomial.eval ((chooseBasis R L).repr x)) at h
  rw [polyCharpoly_coeff_eval, map_zero] at h
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr _ h
  apply (LinearMap.charpoly_monic _).ne_zero

end

/-- Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear family of endomorphisms,
and denote `n := nilRank φ`.

An element `x : L` is *nil-regular* with respect to `φ`
if the `n`-th coefficient of the characteristic polynomial of `φ x` is non-zero. -/
/-
**LinearMap.IsNilRegular** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsNilRegular (x : L) : Prop
参数：x : L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear family of endomorphisms,
and denote `n := nilRank φ`.

An element `x : L` is *nil-regular* with respect to `φ`
if the `n`-th coefficient of the characteristic polynomial of `φ x` is non-zero.
-/
def IsNilRegular (x : L) : Prop :=
  Polynomial.coeff (φ x).charpoly (nilRank φ) ≠ 0

variable (x : L)
/-
**LinearMap.isNilRegular_def** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：isNilRegular_def : IsNilRegular φ x ↔ (Polynomial.coeff (φ x).charpoly (ni
lRank φ) != 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isNilRegular_def :
    IsNilRegular φ x ↔ (Polynomial.coeff (φ x).charpoly (nilRank φ) ≠ 0) := Iff.rfl
/-
**LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero** 是 Mathlib 中的一个
引理，位于命名空间 `LinearMap`。
形式化陈述：isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero : IsNilRegular φ x ↔ M
vPolynomial.eval (b.repr x) ((polyCharpoly φ b).coeff (nilRank φ)) != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsNilRegular.eq_1`：∀ {R : Type u_1} {L : Type u_2} {M : Type u
_3} [inst : CommRing R] [inst_1 : AddCommGroup L]   [inst_2 : _root_.Module R L]
 [inst_3 : AddCom…
· 使用引理 `LinearMap.polyCharpoly_coeff_eval`：polyCharpoly_coeff_eval (x : L) (i : 
Nat) : MvPolynomial.eval (b.repr x) ((polyCharpoly φ b).coeff i) = (φ x).charpol
y.coeff i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero :
    IsNilRegular φ x ↔
    MvPolynomial.eval (b.repr x)
      ((polyCharpoly φ b).coeff (nilRank φ)) ≠ 0 := by
  rw [IsNilRegular, polyCharpoly_coeff_eval]
/-
**LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank** 是 Mathlib 中
的一个引理，位于命名空间 `LinearMap`。
形式化陈述：isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank [Nontrivial R] : Is
NilRegular φ x ↔ (φ x).charpoly.natTrailingDegree = nilRank φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.isNilRegular_def`：isNilRegular_def : IsNilRegular φ x ↔ (Polyn
omial.coeff (φ x).charpoly (nilRank φ) != 0)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Polynomial.natTrailingDegree_le_of_ne_zero`：natTrailingDegree_le_of_ne_z
ero (h : coeff p n != 0) : natTrailingDegree p <= n
· 使用引理 `LinearMap.nilRank_le_natTrailingDegree_charpoly`：nilRank_le_natTrailingD
egree_charpoly (x : L) : nilRank φ <= (φ x).charpoly.natTrailingDegree
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.trailingCoeff_nonzero_iff_nonzero`：trailingCoeff_nonzero_iff_
nonzero : trailingCoeff p != 0 ↔ p != 0
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `LinearMap.charpoly_monic`：charpoly_monic : f.charpoly.Monic
-/
lemma isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank [Nontrivial R] :
    IsNilRegular φ x ↔ (φ x).charpoly.natTrailingDegree = nilRank φ := by
  rw [isNilRegular_def]
  constructor
  · intro h
    exact le_antisymm
      (Polynomial.natTrailingDegree_le_of_ne_zero h)
      (nilRank_le_natTrailingDegree_charpoly φ x)
  · intro h
    rw [← h]
    apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
    apply (LinearMap.charpoly_monic _).ne_zero

section IsDomain

variable [IsDomain R]

open Cardinal Module MvPolynomial Module.Free in
/-
**LinearMap.exists_isNilRegular_of_finrank_le_card** 是 Mathlib 中的一个引理，位于命名空间 `Li
nearMap`。
形式化陈述：exists_isNilRegular_of_finrank_le_card (h : finrank R M <= #R) : exists x 
: L, IsNilRegular φ x
参数：h : finrank R M <= #R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.polyCharpoly_coeff_isHomogeneous`：polyCharpoly_coeff_isHomogen
eous (i j : Nat) (hij : i + j = finrank R M) [Nontrivial R] : ((polyCharpoly φ b
).coeff i).IsHomogeneous j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `LinearMap.nilRank_le_card`：nilRank_le_card {ι : Type*} [Fintype ι] (b : 
Basis ι R M) : nilRank φ <= Fintype.card ι
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `LinearMap.polyCharpoly_coeff_nilRank_ne_zero`：polyCharpoly_coeff_nilRank
_ne_zero : (polyCharpoly φ b).coeff (nilRank φ) != 0
· 使用引理 `MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero_of_le_card`：eq
_zero_of_forall_eval_eq_zero_of_le_card (hF : F.IsHomogeneous n) (h : forall r :
 σ -> R, eval r F = 0) (hnR : n <= #R) : F = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero`：isNilRegu
lar_iff_coeff_polyCharpoly_nilRank_ne_zero : IsNilRegular φ x ↔ MvPolynomial.eva
l (b.repr x) ((polyCharpoly φ b).coeff (nilRank φ))…
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
lemma exists_isNilRegular_of_finrank_le_card (h : finrank R M ≤ #R) :
    ∃ x : L, IsNilRegular φ x := by
  let b := chooseBasis R L
  let bₘ := chooseBasis R M
  let n := Fintype.card (ChooseBasisIndex R M)
  have aux :
    ((polyCharpoly φ b).coeff (nilRank φ)).IsHomogeneous (n - nilRank φ) :=
    polyCharpoly_coeff_isHomogeneous _ b (nilRank φ) (n - nilRank φ)
      (by simp [n, nilRank_le_card φ bₘ, finrank_eq_card_chooseBasisIndex])
  obtain ⟨x, hx⟩ : ∃ r, eval r ((polyCharpoly _ b).coeff (nilRank φ)) ≠ 0 := by
    by_contra! h₀
    apply polyCharpoly_coeff_nilRank_ne_zero φ b
    apply aux.eq_zero_of_forall_eval_eq_zero_of_le_card h₀ (le_trans _ h)
    simp only [n, finrank_eq_card_chooseBasisIndex, Nat.cast_le, Nat.sub_le]
  let c := Finsupp.equivFunOnFinite.symm x
  use b.repr.symm c
  rwa [isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero _ b, LinearEquiv.apply_symm_apply]
/-
**LinearMap.exists_isNilRegular** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：exists_isNilRegular [Infinite R] : exists x : L, IsNilRegular φ x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.exists_isNilRegular_of_finrank_le_card`：exists_isNilRegular_of
_finrank_le_card (h : finrank R M <= #R) : exists x : L, IsNilRegular φ x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.natCast_le_aleph0`：∀ {n : ℕ}, ↑n ≤ Cardinal.aleph0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.infinite_iff`：infinite_iff {α : Type u} : Infinite α ↔ ℵ₀ <= #α
-/
lemma exists_isNilRegular [Infinite R] : ∃ x : L, IsNilRegular φ x := by
  apply exists_isNilRegular_of_finrank_le_card
  exact Cardinal.natCast_le_aleph0.trans <| Cardinal.infinite_iff.mp ‹Infinite R›

end IsDomain

end LinearMap

