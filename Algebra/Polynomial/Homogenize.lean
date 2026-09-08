/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Finsupp.Notation
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogenize a univariate polynomial

In this file we define a function `Polynomial.homogenize p n`
that takes a polynomial `p` and a natural number `n`
and returns a homogeneous bivariate polynomial of degree `n`.

If `n` is at least the degree of `p`, then `(homogenize p n).eval ![x, 1] = p.eval x`.

We use `MvPolynomial (Fin 2) R` to represent bivariate polynomials
instead of `R[X][Y]` (i.e., `Polynomial (Polynomial R)`),
because Mathlib has a theory about homogeneous multivariate polynomials,
but not about homogeneous bivariate polynomials encoded as `R[X][Y]`.
-/

@[expose] public section

open Finset

namespace Polynomial

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- Given a polynomial `p` and a number `n ≥ natDegree p`,
returns a homogeneous bivariate polynomial `q` of degree `n` such that `q(x, 1) = p(x)`.

It is defined as `∑ k + l = n, a_k X_0^k X_1^l`, where `a_k` is the `k`th coefficient of `p`. -/
/-
**Polynomial.homogenize** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：homogenize (p : R[X]) (n : Nat) : MvPolynomial (Fin 2) R
参数：p : R[X]；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a polynomial `p` and a number `n ≥ natDegree p`,
returns a homogeneous bivariate polynomial `q` of degree `n` such that `q(x, 1) 
= p(x)`.

It is defined as `∑ k + l = n, a_k X_0^k X_1^l`, where `a_k` is the `k`th coeffi
cient of `p`.
-/
noncomputable def homogenize (p : R[X]) (n : ℕ) : MvPolynomial (Fin 2) R :=
  ∑ kl ∈ antidiagonal n, .monomial (fun₀ | 0 => kl.1 | 1 => kl.2) (p.coeff kl.1)

@[simp]
/-
**Polynomial.homogenize_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：homogenize_zero (n : Nat) : homogenize (0 : R[X]) n = 0
参数：n : Nat。
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
· 使用定理 `MvPolynomial.monomial_zero`：monomial_zero {s : σ ->₀ Nat} : monomial s (
0 : R) = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homogenize_zero (n : ℕ) : homogenize (0 : R[X]) n = 0 := by
  simp [homogenize]

@[simp]
/-
**Polynomial.homogenize_add** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：homogenize_add (p q : R[X]) (n : Nat) : homogenize (p + q) n = homogenize 
p n + homogenize q n
参数：p q : R[X]；n : Nat。
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
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
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
lemma homogenize_add (p q : R[X]) (n : ℕ) :
    homogenize (p + q) n = homogenize p n + homogenize q n := by
  simp [homogenize, Finset.sum_add_distrib]

@[simp]
/-
**Polynomial.homogenize_smul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：homogenize_smul {S : Type*} [Semiring S] [Module S R] (c : S) (p : R[X]) (
n : Nat) : homogenize (c • p) n = c • homogenize p n
参数：c : S；p : R[X]；n : Nat。
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
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `MvPolynomial.smul_monomial`：smul_monomial {S₁ : Type*} [SMulZeroClass S₁
 R] (r : S₁) : r • monomial s a = monomial s (r • a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homogenize_smul {S : Type*} [Semiring S] [Module S R] (c : S) (p : R[X]) (n : ℕ) :
    homogenize (c • p) n = c • homogenize p n := by
  simp [homogenize, Finset.smul_sum, MvPolynomial.smul_monomial]

/-- `homogenize` as a bundled linear map. -/
@[simps]
/-
**Polynomial.homogenizeLM** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：homogenizeLM (n : Nat) : R[X] ->ₗ[R] MvPolynomial (Fin 2) R where toFun p
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.homogenize_add`：homogenize_add (p q : R[X]) (n : Nat) : homog
enize (p + q) n = homogenize p n + homogenize q n

--- 原说明 ---
`homogenize` as a bundled linear map.
-/
noncomputable def homogenizeLM (n : ℕ) : R[X] →ₗ[R] MvPolynomial (Fin 2) R where
  toFun p := homogenize p n
  map_add' := (homogenize_add · · n)
  map_smul' := (homogenize_smul · · n)

@[simp]
/-
**Polynomial.homogenize_finsetSum** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：homogenize_finsetSum {ι : Type*} (s : Finset ι) (p : ι -> R[X]) (n : Nat) 
: homogenize (∑ i in s, p i) n = ∑ i in s, homogenize (p i) n
参数：s : Finset ι；p : ι -> R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
lemma homogenize_finsetSum {ι : Type*} (s : Finset ι) (p : ι → R[X]) (n : ℕ) :
    homogenize (∑ i ∈ s, p i) n = ∑ i ∈ s, homogenize (p i) n :=
  _root_.map_sum (homogenizeLM n) p s
/-
**Polynomial.homogenize_map** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：homogenize_map {S : Type*} [CommSemiring S] (f : R ->+* S) (p : R[X]) (n :
 Nat) : homogenize (p.map f) n = MvPolynomial.map f (homogenize p n)
参数：f : R ->+* S；p : R[X]；n : Nat。
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
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `MvPolynomial.map_monomial`：map_monomial (s : σ ->₀ Nat) (a : R) : map f 
(monomial s a) = monomial s (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homogenize_map {S : Type*} [CommSemiring S] (f : R →+* S) (p : R[X]) (n : ℕ) :
    homogenize (p.map f) n = MvPolynomial.map f (homogenize p n) := by
  simp [homogenize]

@[simp]
/-
**Polynomial.homogenize_C_mul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：homogenize_C_mul (c : R) (p : R[X]) (n : Nat) : homogenize (C c * p) n = .
C c * homogenize p n
参数：c : R；p : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.C_mul'`：C_mul' (a : R) (f : R[X]) : C a * f = a • f
· 使用引理 `Polynomial.homogenize_smul`：homogenize_smul {S : Type*} [Semiring S] [Mo
dule S R] (c : S) (p : R[X]) (n : Nat) : homogenize (c • p) n = c • homogenize p
 n
· 使用定理 `MvPolynomial.C_mul'`：C_mul' : MvPolynomial.C a * p = a • p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homogenize_C_mul (c : R) (p : R[X]) (n : ℕ) :
    homogenize (C c * p) n = .C c * homogenize p n := by
  simp only [C_mul', homogenize_smul, MvPolynomial.C_mul']

@[simp]
/-
**Polynomial.homogenize_monomial** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：homogenize_monomial {m n : Nat} (h : m <= n) (r : R) : homogenize (monomia
l m r) n = .monomial (fun₀ | 0 => m | 1 => n - m) r
参数：h : m <= n；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.homogenize.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (p 
: Polynomial R) (n : ℕ),   p.homogenize n =     ∑ kl ∈ Finset.HasAntidiagonal.an
tidiagonal n, (M…
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Polynomial.coeff_monomial_same`：coeff_monomial_same (n : Nat) (c : R) : 
(monomial n c).coeff n = c
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
lemma homogenize_monomial {m n : ℕ} (h : m ≤ n) (r : R) :
    homogenize (monomial m r) n = .monomial (fun₀ | 0 => m | 1 => n - m) r := by
  rw [homogenize, Finset.sum_eq_single (a := (m, n - m))]
  · simp
  · aesop (add simp coeff_monomial)
  · simp [h]
/-
**Polynomial.homogenize_monomial_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：homogenize_monomial_of_lt {m n : Nat} (h : n < m) (r : R) : homogenize (mo
nomial m r) n = 0
参数：h : n < m；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.homogenize.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (p 
: Polynomial R) (n : ℕ),   p.homogenize n =     ∑ kl ∈ Finset.HasAntidiagonal.an
tidiagonal n, (M…
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma homogenize_monomial_of_lt {m n : ℕ} (h : n < m) (r : R) :
    homogenize (monomial m r) n = 0 := by
  rw [homogenize]
  apply Finset.sum_eq_zero
  aesop (add simp coeff_monomial)

@[simp]
/-
**Polynomial.homogenize_X_pow** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：homogenize_X_pow {m n : Nat} (h : m <= n) : homogenize (X ^ m : R[X]) n = 
.X 0 ^ m * .X 1 ^ (n - m)
参数：h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.X_pow_eq_monomial`：X_pow_eq_monomial (n) : X ^ n = monomial n
 (1 : R)
· 使用引理 `Polynomial.homogenize_monomial`：homogenize_monomial {m n : Nat} (h : m <
= n) (r : R) : homogenize (monomial m r) n = .monomial (fun₀ | 0 => m | 1 => n -
 m) r
· 使用引理 `Finsupp.update_eq_add_single`：update_eq_add_single {f : ι ->₀ M} {a : ι}
 (h : f a = 0) (b : M) : f.update a b = f + single a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.monomial_single_add`：monomial_single_add : monomial (Finsup
p.single n e + s) a = X n ^ e * monomial s a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.X_pow_eq_monomial`：X_pow_eq_monomial : X n ^ e = monomial (
Finsupp.single n e) (1 : R)
-/
lemma homogenize_X_pow {m n : ℕ} (h : m ≤ n) :
    homogenize (X ^ m : R[X]) n = .X 0 ^ m * .X 1 ^ (n - m) := by
  rw [X_pow_eq_monomial, homogenize_monomial h, Finsupp.update_eq_add_single (by simp),
    MvPolynomial.monomial_single_add, ← MvPolynomial.X_pow_eq_monomial]

@[simp]
/-
**Polynomial.homogenize_X** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：homogenize_X {n : Nat} (hn : n != 0) : homogenize (X : R[X]) n = .X 0 * .X
 1 ^ (n - 1)
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `Polynomial.homogenize_X_pow`：homogenize_X_pow {m n : Nat} (h : m <= n) :
 homogenize (X ^ m : R[X]) n = .X 0 ^ m * .X 1 ^ (n - m)
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
-/
lemma homogenize_X {n : ℕ} (hn : n ≠ 0) : homogenize (X : R[X]) n = .X 0 * .X 1 ^ (n - 1) := by
  rw [← pow_one X, homogenize_X_pow, pow_one]
  rwa [Nat.one_le_iff_ne_zero]

@[simp]
/-
**Polynomial.homogenize_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：homogenize_C (c : R) (n : Nat) : homogenize (.C c) n = .C c * .X 1 ^ n
参数：c : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.C_mul_X_pow_eq_monomial`：C_mul_X_pow_eq_monomial {s : σ} {a
 : R} {n : Nat} : C a * X s ^ n = monomial (Finsupp.single s n) a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用引理 `Polynomial.homogenize_monomial`：homogenize_monomial {m n : Nat} (h : m <
= n) (r : R) : homogenize (monomial m r) n = .monomial (fun₀ | 0 => m | 1 => n -
 m) r
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
lemma homogenize_C (c : R) (n : ℕ) : homogenize (.C c) n = .C c * .X 1 ^ n := by
  simpa [MvPolynomial.C_mul_X_pow_eq_monomial] using homogenize_monomial (Nat.zero_le n) c

@[simp]
/-
**Polynomial.homogenize_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：homogenize_one (n : Nat) : homogenize (1 : R[X]) n = .X 1 ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用引理 `Polynomial.homogenize_C`：homogenize_C (c : R) (n : Nat) : homogenize (.C
 c) n = .C c * .X 1 ^ n
-/
lemma homogenize_one (n : ℕ) : homogenize (1 : R[X]) n = .X 1 ^ n := by
  simpa using homogenize_C (1 : R) n
/-
**Polynomial.coeff_homogenize** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：coeff_homogenize (p : R[X]) (n : Nat) (m : Fin 2 ->₀ Nat) : (homogenize p 
n).coeff m = if m 0 + m 1 = n then coeff p (m 0) else 0
参数：p : R[X]；n : Nat；m : Fin 2 ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.homogenize_add`：homogenize_add (p q : R[X]) (n : Nat) : homog
enize (p + q) n = homogenize p n + homogenize q n
· 使用定理 `MvPolynomial.coeff_add`：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p + q) = coeff m p + coeff m q
· 使用定理 `ite_add_ite`：∀ {α : Type u_2} (P : Prop) [inst : Decidable P] [inst_1 : 
Add α] (a b c d : α),   ((if P then a else b) + if P then c else d) = if P then 
a…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用引理 `Polynomial.homogenize_monomial`：homogenize_monomial {m n : Nat} (h : m <
= n) (r : R) : homogenize (monomial m r) n = .monomial (fun₀ | 0 => m | 1 => n -
 m) r
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_update`：coe_update [DecidableEq α] : (f.update a b : α -> M)
 = Function.update f a b
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 49 条，此处仅展示前 30 条）
-/
lemma coeff_homogenize (p : R[X]) (n : ℕ) (m : Fin 2 →₀ ℕ) :
    (homogenize p n).coeff m = if m 0 + m 1 = n then coeff p (m 0) else 0 := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp [*, ite_add_ite]
  | monomial k c =>
    rcases le_or_gt k n with hkn | hnk
    · rw [homogenize_monomial hkn, coeff_monomial, MvPolynomial.coeff_monomial]
      have : (fun₀ | 0 => m 0 | 1 => m 1) = m := by ext i; fin_cases i <;> simp
      aesop
    · aesop (add simp homogenize_monomial_of_lt) (add simp coeff_monomial)
/-
**Polynomial.eq_zero_of_homogenize_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial
`。
形式化陈述：eq_zero_of_homogenize_eq_zero {p : R[X]} {n : Nat} (hn : p.natDegree <= n)
 (h : p.homogenize n = 0) : p = 0
参数：hn : p.natDegree <= n；h : p.homogenize n = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.coeff_homogenize`：coeff_homogenize (p : R[X]) (n : Nat) (m : 
Fin 2 ->₀ Nat) : (homogenize p n).coeff m = if m 0 + m 1 = n then coeff p (m 0) 
else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_update`：coe_update [DecidableEq α] : (f.update a b : α -> M)
 = Function.update f a b
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Nat.add_sub_of_le`：∀ {a b : ℕ}, a ≤ b → a + (b - a) = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
-/
lemma eq_zero_of_homogenize_eq_zero {p : R[X]} {n : ℕ} (hn : p.natDegree ≤ n)
    (h : p.homogenize n = 0) :
    p = 0 := by
  ext i
  simp only [coeff_zero]
  rcases le_or_gt i p.natDegree with H | H
  · have : p.coeff i = (p.homogenize n).coeff fun₀ | 0 => i | 1 => n - i := by
      simp [coeff_homogenize, Nat.add_sub_of_le (H.trans hn)]
    simp [this, h]
  · exact coeff_eq_zero_of_natDegree_lt H
/-
**Polynomial.homogenize_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：homogenize_eq_zero_iff {p : R[X]} {n : Nat} (hn : p.natDegree <= n) : p.ho
mogenize n = 0 ↔ p = 0
参数：hn : p.natDegree <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.eq_zero_of_homogenize_eq_zero`：eq_zero_of_homogenize_eq_zero 
{p : R[X]} {n : Nat} (hn : p.natDegree <= n) (h : p.homogenize n = 0) : p = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.homogenize_zero`：homogenize_zero (n : Nat) : homogenize (0 : 
R[X]) n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma homogenize_eq_zero_iff {p : R[X]} {n : ℕ} (hn : p.natDegree ≤ n) :
    p.homogenize n = 0 ↔ p = 0 :=
  ⟨eq_zero_of_homogenize_eq_zero hn, by simp +contextual⟩
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eval₂_homogenize_of_eq_one {S : Type*} [CommSemiring S] {p : R[X]} {n : ℕ}
    (hn : natDegree p ≤ n) (f : R →+* S) (g : Fin 2 → S) (hg : g 1 = 1) :
    MvPolynomial.eval₂ f g (p.homogenize n) = p.eval₂ f (g 0) := by
  apply Polynomial.induction_with_natDegree_le
    (fun p ↦ MvPolynomial.eval₂ f g (p.homogenize n) = p.eval₂ f (g 0)) (N := n)
  · simp
  · simp +contextual [hg]
  · simp +contextual
  · assumption
/-
**Polynomial.aeval_homogenize_of_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：aeval_homogenize_of_eq_one {A : Type*} [CommSemiring A] [Algebra R A] {p :
 R[X]} {n : Nat} (hn : natDegree p <= n) (g : Fin 2 -> A) (hg : g 1 = 1) : MvPol
ynomial.aeval g (p.homogenize n) = aeval (g 0) p
参数：hn : natDegree p <= n；g : Fin 2 -> A；hg : g 1 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Polynomial.eval₂_homogenize_of_eq_one`：eval₂_homogenize_of_eq_one {S : T
ype*} [CommSemiring S] {p : R[X]} {n : Nat} (hn : natDegree p <= n) (f : R ->+* 
S) (g : Fin 2 -> S) (hg : g…
-/
lemma aeval_homogenize_of_eq_one {A : Type*} [CommSemiring A] [Algebra R A] {p : R[X]} {n : ℕ}
    (hn : natDegree p ≤ n) (g : Fin 2 → A) (hg : g 1 = 1) :
    MvPolynomial.aeval g (p.homogenize n) = aeval (g 0) p := by
  apply eval₂_homogenize_of_eq_one <;> assumption

/-- If `deg p ≤ n`, then `homogenize p n (x, 1) = p x`. -/
@[simp]
/-
**Polynomial.aeval_homogenize_X_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：aeval_homogenize_X_one (p : R[X]) {n : Nat} (hn : natDegree p <= n) : MvPo
lynomial.aeval ![X, 1] (p.homogenize n) = p
参数：p : R[X]；hn : natDegree p <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.aeval_homogenize_of_eq_one`：aeval_homogenize_of_eq_one {A : T
ype*} [CommSemiring A] [Algebra R A] {p : R[X]} {n : Nat} (hn : natDegree p <= n
) (g : Fin 2 -> A) (hg : g …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.aeval_X_left`：aeval_X_left : aeval (X : R[X]) = AlgHom.id R R
[X]

--- 原说明 ---
If `deg p ≤ n`, then `homogenize p n (x, 1) = p x`.
-/
lemma aeval_homogenize_X_one (p : R[X]) {n : ℕ} (hn : natDegree p ≤ n) :
    MvPolynomial.aeval ![X, 1] (p.homogenize n) = p := by
  rw [aeval_homogenize_of_eq_one] <;> simp [*]

@[simp]
/-
**Polynomial.isHomogeneous_homogenize** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isHomogeneous_homogenize {n : Nat} (p : R[X]) : (p.homogenize n).IsHomogen
eous n
参数：p : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.IsHomogeneous.sum`：sum {ι : Type*} (s : Finset ι) (φ : ι ->
 MvPolynomial σ R) (n : Nat) (h : forall i in s, IsHomogeneous (φ i) n) : IsHomo
geneous (∑ i in s, φ…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MvPolynomial.isHomogeneous_monomial`：isHomogeneous_monomial {d : σ ->₀ N
at} (r : R) {n : Nat} (hn : d.degree = n) : IsHomogeneous (monomial d r) n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.update_eq_add_single`：update_eq_add_single {f : ι ->₀ M} {a : ι}
 (h : f a = 0) (b : M) : f.update a b = f + single a b
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.degree_single`：degree_single (a : σ) (r : R) : (Finsupp.single a
 r).degree = r
-/
lemma isHomogeneous_homogenize {n : ℕ} (p : R[X]) : (p.homogenize n).IsHomogeneous n := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ ?_
  simp only [Prod.forall, mem_antidiagonal]
  rintro a b rfl
  apply MvPolynomial.isHomogeneous_monomial
  simp [Finsupp.update_eq_add_single]
/-
**Polynomial.homogenize_eq_of_isHomogeneous** 是 Mathlib 中的一个引理，位于命名空间 `Polynomia
l`。
形式化陈述：homogenize_eq_of_isHomogeneous {p : R[X]} {n : Nat} {q : MvPolynomial (Fin
 2) R} (hq : q.IsHomogeneous n) (hpq : MvPolynomial.aeval ![X, 1] q = p) : p.hom
ogenize n = q
参数：Fin 2；hq : q.IsHomogeneous n；hpq : MvPolynomial.aeval ![X, 1] q = p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.as_sum`：as_sum (p : MvPolynomial σ R) : p = ∑ v in p.suppor
t, monomial v (coeff v p)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.aeval_sum`：aeval_sum {ι : Type*} (s : Finset ι) (φ : ι -> M
vPolynomial σ R) : aeval f (∑ i in s, φ i) = ∑ i in s, aeval f (φ i)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPolynomial.aeval_monomial`：aeval_monomial (g : σ -> S₁) (d : σ ->₀ Nat
) (r : R) : aeval g (monomial d r) = algebraMap _ _ r * d.prod fun i k => g i ^ 
k
· 使用引理 `Polynomial.homogenize_finsetSum`：homogenize_finsetSum {ι : Type*} (s : F
inset ι) (p : ι -> R[X]) (n : Nat) : homogenize (∑ i in s, p i) n = ∑ i in s, ho
mogenize (p i) n
· 使用引理 `Polynomial.homogenize_C_mul`：homogenize_C_mul (c : R) (p : R[X]) (n : Na
t) : homogenize (C c * p) n = .C c * homogenize p n
· 使用定理 `MvPolynomial.monomial_eq`：monomial_eq : monomial s a = C a * (s.prod fun
 n e => X n ^ e : MvPolynomial σ R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.prod_fintype`：prod_fintype [Fintype α] (f : α ->₀ M) (g : α -> M
 -> N) (h : forall i, g i 0 = 1) : f.prod g = ∏ i, g i (f i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Fin.prod_univ_two`：prod_univ_two (f : Fin 2 -> M) : ∏ i, f i = f 0 * f 1
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用引理 `Polynomial.homogenize_X_pow`：homogenize_X_pow {m n : Nat} (h : m <= n) :
 homogenize (X ^ m : R[X]) n = .X 0 ^ m * .X 1 ^ (n - m)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
（共 33 条，此处仅展示前 30 条）
-/
lemma homogenize_eq_of_isHomogeneous {p : R[X]} {n : ℕ} {q : MvPolynomial (Fin 2) R}
    (hq : q.IsHomogeneous n) (hpq : MvPolynomial.aeval ![X, 1] q = p) :
    p.homogenize n = q := by
  subst p
  rw [q.as_sum]
  simp only [MvPolynomial.aeval_sum, MvPolynomial.aeval_monomial, ← C_eq_algebraMap,
    homogenize_finsetSum, homogenize_C_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [MvPolynomial.monomial_eq]
  congr 1
  obtain rfl : m.weight 1 = n := hq <| by simpa using hm
  simp [Finsupp.prod_fintype, Finsupp.weight_apply, Finsupp.sum_fintype, Fin.prod_univ_two,
    Fin.sum_univ_two]
/-
**Polynomial.homogenize_mul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：homogenize_mul (p q : R[X]) {m n : Nat} (hm : natDegree p <= m) (hn : natD
egree q <= n) : homogenize (p * q) (m + n) = homogenize p m * homogenize q n
参数：p q : R[X]；hm : natDegree p <= m；hn : natDegree q <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.homogenize_eq_of_isHomogeneous`：homogenize_eq_of_isHomogeneou
s {p : R[X]} {n : Nat} {q : MvPolynomial (Fin 2) R} (hq : q.IsHomogeneous n) (hp
q : MvPolynomial.aeval ![X, 1] …
· 使用定理 `MvPolynomial.IsHomogeneous.mul`：mul (hφ : IsHomogeneous φ m) (hψ : IsHom
ogeneous ψ n) : IsHomogeneous (φ * ψ) (m + n)
· 使用引理 `Polynomial.isHomogeneous_homogenize`：isHomogeneous_homogenize {n : Nat} 
(p : R[X]) : (p.homogenize n).IsHomogeneous n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Polynomial.aeval_homogenize_X_one`：aeval_homogenize_X_one (p : R[X]) {n 
: Nat} (hn : natDegree p <= n) : MvPolynomial.aeval ![X, 1] (p.homogenize n) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homogenize_mul (p q : R[X]) {m n : ℕ} (hm : natDegree p ≤ m) (hn : natDegree q ≤ n) :
    homogenize (p * q) (m + n) = homogenize p m * homogenize q n := by
  apply homogenize_eq_of_isHomogeneous
  · apply_rules [MvPolynomial.IsHomogeneous.mul, isHomogeneous_homogenize]
  · simp [*]
/-
**Polynomial.homogenize_finsetProd** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：homogenize_finsetProd {ι : Type*} {s : Finset ι} {p : ι -> R[X]} {n : ι ->
 Nat} (h : forall i in s, (p i).natDegree <= n i) : homogenize (∏ i in s, p i) (
∑ i in s, n i) = ∏ i in s, homogenize (p i) (n i)
参数：h : forall i in s, (p i).natDegree <= n i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Polynomial.homogenize_one`：homogenize_one (n : Nat) : homogenize (1 : R[
X]) n = .X 1 ^ n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用引理 `Polynomial.homogenize_mul`：homogenize_mul (p q : R[X]) {m n : Nat} (hm :
 natDegree p <= m) (hn : natDegree q <= n) : homogenize (p * q) (m + n) = homoge
nize p m * homo…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.natDegree_prod_le`：natDegree_prod_le : (∏ i in s, f i).natDeg
ree <= ∑ i in s, (f i).natDegree
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma homogenize_finsetProd {ι : Type*} {s : Finset ι} {p : ι → R[X]} {n : ι → ℕ}
    (h : ∀ i ∈ s, (p i).natDegree ≤ n i) :
    homogenize (∏ i ∈ s, p i) (∑ i ∈ s, n i) = ∏ i ∈ s, homogenize (p i) (n i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ihs =>
    simp only [prod_cons, sum_cons, forall_mem_cons] at *
    rw [homogenize_mul _ _ h.1, ihs h.2]
    exact (natDegree_prod_le _ _).trans (sum_le_sum h.2)
/-
**Polynomial.homogenize_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：homogenize_dvd [NoZeroDivisors R] {p q : R[X]} (h : p ∣ q) : homogenize p 
p.natDegree ∣ homogenize q q.natDegree
参数：h : p ∣ q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.homogenize_zero`：homogenize_zero (n : Nat) : homogenize (0 : 
R[X]) n = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `Polynomial.natDegree_mul`：natDegree_mul (hp : p != 0) (hq : q != 0) : (p
 * q).natDegree = p.natDegree + q.natDegree
· 使用引理 `Polynomial.homogenize_mul`：homogenize_mul (p q : R[X]) {m n : Nat} (hm :
 natDegree p <= m) (hn : natDegree q <= n) : homogenize (p * q) (m + n) = homoge
nize p m * homo…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
lemma homogenize_dvd [NoZeroDivisors R] {p q : R[X]} (h : p ∣ q) :
    homogenize p p.natDegree ∣ homogenize q q.natDegree := by
  rcases h with ⟨r, rfl⟩
  obtain rfl | rfl | ⟨hp₀, hr₀⟩ : p = 0 ∨ r = 0 ∨ p ≠ 0 ∧ r ≠ 0 := by tauto
  · simp
  · simp
  · rw [natDegree_mul hp₀ hr₀, homogenize_mul _ _ le_rfl le_rfl]
    apply dvd_mul_right

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

@[simp]
/-
**Polynomial.homogenize_neg** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：homogenize_neg (p : R[X]) (n : Nat) : (-p).homogenize n = -p.homogenize n
参数：p : R[X]；n : Nat。
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
lemma homogenize_neg (p : R[X]) (n : ℕ) : (-p).homogenize n = -p.homogenize n :=
  map_neg (homogenizeLM n) p

@[simp]
/-
**Polynomial.homogenize_sub** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：homogenize_sub (p q : R[X]) (n : Nat) : (p - q).homogenize n = p.homogeniz
e n - q.homogenize n
参数：p q : R[X]；n : Nat。
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
lemma homogenize_sub (p q : R[X]) (n : ℕ) :
    (p - q).homogenize n = p.homogenize n - q.homogenize n :=
  map_sub (homogenizeLM n) p q

end CommRing

section Semifield

variable {K : Type*} [Semifield K]

/-
**Polynomial.eval_homogenize** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：eval_homogenize {p : K[X]} {n : Nat} (hn : p.natDegree <= n) (x : Fin 2 ->
 K) (hx : x 1 != 0) : MvPolynomial.eval x (p.homogenize n) = p.eval (x 0 / x 1) 
* x 1 ^ n
参数：hn : p.natDegree <= n；x : Fin 2 -> K；hx : x 1 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`：∀ {M : Type u_3} [inst
 : AddCommMonoid M] (f : ℕ × ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.ant
idiagonal n, f ij = ∑ k ∈ Finset.range…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPolynomial.eval_sum`：eval_sum {ι : Type*} (s : Finset ι) (f : ι -> MvP
olynomial σ R) (g : σ -> R) : eval g (∑ i in s, f i) = ∑ i in s, eval g (f i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_eq_sum_range'`：eval_eq_sum_range' {p : R[X]} {n : Nat} (
hn : p.natDegree < n) (x : R) : p.eval x = ∑ i in Finset.range n, p.coeff i * x 
^ i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `MvPolynomial.eval_monomial`：eval_monomial : eval f (monomial s a) = a * 
s.prod fun n e => f n ^ e
· 使用引理 `Finsupp.update_eq_add_single`：update_eq_add_single {f : ι ->₀ M} {a : ι}
 (h : f a = 0) (b : M) : f.update a b = f + single a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.prod_add_index'`：prod_add_index' [AddZeroClass M] [CommMonoid N]
 {f g : α ->₀ M} {h : α -> M -> N} (h_zero : forall a, h a 0 = 1) (h_add : foral
l a b₁ b₂, h …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Finsupp.prod_single_index`：prod_single_index {a : α} {b : M} {h : α -> M
 -> N} (h_zero : h a 0 = 1) : (single a b).prod h = h a b
· 使用引理 `pow_sub₀`：pow_sub₀ (a : G₀) (ha : a != 0) (h : n <= m) : a ^ (m - n) = a
 ^ m * (a ^ n)⁻¹
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 53 条，此处仅展示前 30 条）
-/
lemma eval_homogenize {p : K[X]} {n : ℕ} (hn : p.natDegree ≤ n) (x : Fin 2 → K) (hx : x 1 ≠ 0) :
    MvPolynomial.eval x (p.homogenize n) = p.eval (x 0 / x 1) * x 1 ^ n := by
  simp only [homogenize, Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hn),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul, MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [MvPolynomial.eval_monomial, Finsupp.update_eq_add_single, Finsupp.prod_add_index',
    Finsupp.prod_single_index, Finsupp.prod_single_index, pow_sub₀]
  · ring
  all_goals simp_all [pow_add]

end Semifield

section projectivize

variable {R : Type*} [CommSemiring R]

/-- Given a polynomial `p : R[X]`, this is the vector `![p₀, p₁]` of homogeneous bivariate
polynomials of degree `p.natDegree` such that `p(x) = p₀(x,1)/p₁(x,1)` and `p₁` is a monomial. -/
noncomputable
/-
**Polynomial.toTupleMvPolynomial** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：toTupleMvPolynomial (p : R[X]) : Fin 2 -> MvPolynomial (Fin 2) R
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toTupleMvPolynomial (p : R[X]) : Fin 2 → MvPolynomial (Fin 2) R :=
  ![p.homogenize p.natDegree, (MvPolynomial.X 1) ^ p.natDegree]
/-
**Polynomial.toTupleMvPolynomial_zero_eq** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：toTupleMvPolynomial_zero_eq (p : R[X]) : p.toTupleMvPolynomial 0 = p.homog
enize p.natDegree
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma toTupleMvPolynomial_zero_eq (p : R[X]) :
    p.toTupleMvPolynomial 0 = p.homogenize p.natDegree :=
  rfl
/-
**Polynomial.toTupleMvPolynomial_one_eq** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：toTupleMvPolynomial_one_eq (p : R[X]) : p.toTupleMvPolynomial 1 = (MvPolyn
omial.X 1) ^ p.natDegree
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma toTupleMvPolynomial_one_eq (p : R[X]) :
    p.toTupleMvPolynomial 1 = (MvPolynomial.X 1) ^ p.natDegree :=
  rfl
/-
**Polynomial.isHomogeneous_toTupleMvPolynomial** 是 Mathlib 中的一个引理，位于命名空间 `Polyno
mial`。
形式化陈述：isHomogeneous_toTupleMvPolynomial (p : R[X]) (i : Fin 2) : (p.toTupleMvPol
ynomial i).IsHomogeneous p.natDegree
参数：p : R[X]；i : Fin 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MvPolynomial.isHomogeneous_X_pow`：∀ {σ : Type u_1} {R : Type u_3} [inst 
: CommSemiring R] (i : σ) (n : ℕ), (MvPolynomial.X i ^ n).IsHomogeneous n
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma isHomogeneous_toTupleMvPolynomial (p : R[X]) (i : Fin 2) :
    (p.toTupleMvPolynomial i).IsHomogeneous p.natDegree := by
  fin_cases i
  · simp [toTupleMvPolynomial]
  · simpa [toTupleMvPolynomial] using MvPolynomial.isHomogeneous_X_pow 1 p.natDegree

@[deprecated (since := "2026-04-06")]
alias isHomogenous_toTupleMvPolynomial := isHomogeneous_toTupleMvPolynomial
/-
**Polynomial.eval_X_toTupleMvPolynomial_zero_eq** 是 Mathlib 中的一个引理，位于命名空间 `Polyn
omial`。
形式化陈述：eval_X_toTupleMvPolynomial_zero_eq (p : R[X]) : MvPolynomial.aeval ![X, 1]
 (p.toTupleMvPolynomial 0) = p * MvPolynomial.aeval ![X, 1] (p.toTupleMvPolynomi
al 1)
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.aeval_homogenize_X_one`：aeval_homogenize_X_one (p : R[X]) {n 
: Nat} (hn : natDegree p <= n) : MvPolynomial.aeval ![X, 1] (p.homogenize n) = p
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eval_X_toTupleMvPolynomial_zero_eq (p : R[X]) :
    MvPolynomial.aeval ![X, 1] (p.toTupleMvPolynomial 0) =
      p * MvPolynomial.aeval ![X, 1] (p.toTupleMvPolynomial 1) := by
  simp [toTupleMvPolynomial]
/-
**Polynomial.eval_eq_div_eval_toTupleMvPolynomial** 是 Mathlib 中的一个引理，位于命名空间 `Pol
ynomial`。
形式化陈述：eval_eq_div_eval_toTupleMvPolynomial {R : Type*} [Field R] (p : R[X]) (x :
 R) : p.eval x = (p.toTupleMvPolynomial 0).eval ![x, 1] / (p.toTupleMvPolynomial
 1).eval ![x, 1]
参数：p : R[X]；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Polynomial.eval_homogenize`：eval_homogenize {p : K[X]} {n : Nat} (hn : p
.natDegree <= n) (x : Fin 2 -> K) (hx : x 1 != 0) : MvPolynomial.eval x (p.homog
enize n) = p.eva…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MvPolynomial.eval_X`：eval_X : forall n, eval f (X n) = f n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eval_eq_div_eval_toTupleMvPolynomial {R : Type*} [Field R] (p : R[X]) (x : R) :
    p.eval x =
      (p.toTupleMvPolynomial 0).eval ![x, 1] / (p.toTupleMvPolynomial 1).eval ![x, 1] := by
  simp [toTupleMvPolynomial, eval_homogenize]
/-
**Polynomial.sum_eq_natDegree_of_mem_support_homogenize** 是 Mathlib 中的一个引理，位于命名空
间 `Polynomial`。
形式化陈述：sum_eq_natDegree_of_mem_support_homogenize (p : R[X]) {s : Fin 2 ->₀ Nat} 
(hs : s in (p.homogenize p.natDegree).support) : s 0 + s 1 = p.natDegree
参数：p : R[X]；hs : s in (p.homogenize p.natDegree).support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support`：degree_eq_sum_deg_
support (hφ : φ.IsHomogeneous n) {s : σ ->₀ Nat} (hs : s in φ.support) : n = ∑ i
 in s.support, s i
· 使用引理 `Polynomial.isHomogeneous_homogenize`：isHomogeneous_homogenize {n : Nat} 
(p : R[X]) : (p.homogenize n).IsHomogeneous n
· 使用定理 `Finsupp.degree_eq_sum`：degree_eq_sum [Fintype σ] (f : σ ->₀ R) : f.degre
e = ∑ i, f i
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_eq_natDegree_of_mem_support_homogenize (p : R[X]) {s : Fin 2 →₀ ℕ}
    (hs : s ∈ (p.homogenize p.natDegree).support) :
    s 0 + s 1 = p.natDegree := by
  simp [(isHomogeneous_homogenize p).degree_eq_sum_deg_support hs, ← Finsupp.degree_apply,
        Finsupp.degree_eq_sum]

/-- Summing a function over the coefficients of the homogenization of a polynomial `p`
(of degree `p.natDegree`) gives the same result as summing over the coefficients of `p`. -/
/-
**Polynomial.finsuppSum_homogenize_eq** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：finsuppSum_homogenize_eq {M : Type*} [AddCommMonoid M] (p : R[X]) {f : R -
> M} : (AddMonoidAlgebra.coeff <| p.homogenize p.natDegree).sum (fun _ c => f c)
 = p.sum fun _ c => f c
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.sum_def`：sum_def {A} [AddCommMonoid A] {p : MvPolynomial σ 
R} {b : (σ ->₀ Nat) -> R -> A} : (AddMonoidAlgebra.coeff p).sum b = ∑ m in p.sup
port, b m …
· 使用定理 `Polynomial.sum_def`：sum_def {S : Type*} [AddCommMonoid S] (p : R[X]) (f 
: Nat -> R -> S) : p.sum f = ∑ n in p.support, f n (p.coeff n)
· 使用定理 `Finset.sum_nbij'`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst :
 AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : ι
 → κ) …
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Polynomial.coeff_homogenize`：coeff_homogenize (p : R[X]) (n : Nat) (m : 
Fin 2 ->₀ Nat) : (homogenize p n).coeff m = if m 0 + m 1 = n then coeff p (m 0) 
else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用引理 `Polynomial.sum_eq_natDegree_of_mem_support_homogenize`：sum_eq_natDegree_
of_mem_support_homogenize (p : R[X]) {s : Fin 2 ->₀ Nat} (hs : s in (p.homogeniz
e p.natDegree).support) : s 0 + s 1 = p.nat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_update`：coe_update [DecidableEq α] : (f.update a b : α -> M)
 = Function.update f a b
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
· 使用定理 `Nat.add_sub_of_le`：∀ {a b : ℕ}, a ≤ b → a + (b - a) = b
· 使用定理 `Polynomial.le_natDegree_of_mem_supp`：le_natDegree_of_mem_supp (a : Nat) 
: a in p.support -> a <= natDegree p

--- 原说明 ---
Summing a function over the coefficients of the homogenization of a polynomial `
p`
(of degree `p.natDegree`) gives the same result as summing over the coefficients
 of `p`.
-/
lemma finsuppSum_homogenize_eq {M : Type*} [AddCommMonoid M] (p : R[X]) {f : R → M} :
    (AddMonoidAlgebra.coeff <| p.homogenize p.natDegree).sum (fun _ c ↦ f c) =
      p.sum fun _ c ↦ f c := by
  rw [MvPolynomial.sum_def, sum_def p]
  -- We set up a bijection between the sets indexing the terms on both sides
  -- and show that it maps the terms in the one sum to those in the other.
  refine Finset.sum_nbij' (fun s ↦ s 0) (fun n ↦ fun₀ | 0 => n | 1 => p.natDegree - n)
    (fun s hs ↦ ?_) (fun n hn ↦ ?_) (fun s hs ↦ ?_) (fun n hn ↦ by simp)
    fun s hs ↦ ?_
  · simpa [coeff_homogenize, sum_eq_natDegree_of_mem_support_homogenize p hs] using hs
  · simpa [coeff_homogenize, mem_support_iff.mp hn]
      using Nat.add_sub_of_le <| le_natDegree_of_mem_supp n hn
  · -- speeds up `grind` quite a bit
    grind only [= Finsupp.update_apply, = Finsupp.single_apply,
      sum_eq_natDegree_of_mem_support_homogenize p hs]
  · simp [coeff_homogenize, sum_eq_natDegree_of_mem_support_homogenize p hs]

end projectivize

end Polynomial

